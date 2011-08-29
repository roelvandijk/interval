{-# LANGUAGE NoImplicitPrelude, UnicodeSyntax #-}

module Numeric.Interval
    ( I, (…), (...)
    , singleton, null
    , bounds, inf, sup
    , (∈),  (∋),  (∉),  (∌)
    , (∈?), (∋?), (∉?), (∌?)
    , (⊂),  (⊃),  (⊄),  (⊅)
    , (⊆),  (⊇),  (⊈),  (⊉)
    , (∪)
    ) where

--------------------------------------------------------------------------------
-- Imports
--------------------------------------------------------------------------------

-- from base:
import Control.Applicative ( (<$>), (<*>) )
import Control.Monad       ( foldM )
import Data.Bool           ( Bool(False, True), otherwise, not )
import Data.Eq             ( Eq, (==) )
import Data.Function       ( flip )
import Data.Maybe          ( Maybe(Nothing, Just) )
import Data.Ord            ( Ord, (<), (>), min, max )
import Data.Tuple          ( fst, snd )
import Prelude             ( Num, (+), (*), (-), negate, abs, signum
                           , fromInteger
                           )
import Text.Show           ( Show )

-- from base-unicode-symbols:
import Data.Bool.Unicode     ( (∧), (∨) )
import Data.Eq.Unicode       ( (≡), (≢) )
import Data.Ord.Unicode      ( (≤), (≥) )
import Data.Function.Unicode ( (∘) )
import Prelude.Unicode       ( (⋅) )

-- from logfloat:
import Data.Number.PartialOrd  ( PartialOrd, ge, le, minPO, maxPO )


--------------------------------------------------------------------------------
-- Intervals
--------------------------------------------------------------------------------

-- An interval: n ∈ I a b ≝ a ≤ n ≤ b
data I α = I α α deriving (Show)

--------------------------------------------------------------------------------

(…) ∷ α → α → I α
(…) = I

(...) ∷ α → α → I α
(...) = I

infix 8 …
infix 8 ...

singleton ∷ α → I α
singleton x = I x x

-- null i → ∀ x. x ∉ i
null ∷ (Num α) ⇒ I α → Bool
null (I x y) = signum (x - y) ≡ 1
             ∨ x ≢ x -- Hack because the Eq instances of Float and
             ∨ y ≢ y -- Double violate the laws of Eq.

instance (Num α) ⇒ Eq (I α) where
    i₁@(I x₁ y₁) == i₂@(I x₂ y₂)
        | null i₁ ∧ null i₂ = True
        | otherwise         = x₁ ≡ x₂ ∧ y₁ ≡ y₂


--------------------------------------------------------------------------------

bounds ∷ I α → (α, α)
bounds (I a b) = (a, b)

inf, sup ∷ I α → α
-- | Infimum
inf = fst ∘ bounds
-- | Supremum
sup = snd ∘ bounds

empty ∷ (Num α) ⇒ I α
empty = I 1 0

--------------------------------------------------------------------------------

(∈) ∷ (Ord α) ⇒ α → I α → Bool
n ∈ I x y = n ≥ x ∧ n ≤ y

(∋) ∷ (Ord α) ⇒ I α → α → Bool
(∋) = flip (∈)

(∉) ∷ (Ord α) ⇒ α → I α → Bool
n ∉ i = not (n ∈ i)

(∌) ∷ (Ord α) ⇒ I α → α → Bool
(∌) = flip (∉)

infix 4 ∈, ∋, ∉, ∌

(∈?) ∷ (PartialOrd α) ⇒ α → I α → Maybe Bool
n ∈? I x y = (∧) <$> ge n x <*> le n y

(∋?) ∷ (PartialOrd α) ⇒ I α → α → Maybe Bool
(∋?) = flip (∈?)

(∉?) ∷ (PartialOrd α) ⇒ α → I α → Maybe Bool
n ∉? i = not <$> (n ∈? i)

(∌?) ∷ (PartialOrd α) ⇒ I α → α → Maybe Bool
(∌?) = flip (∉?)

infix 4 ∈?, ∋?, ∉?, ∌?

--------------------------------------------------------------------------------

(⊂) ∷ (Num α, Ord α) ⇒ I α → I α → Bool
i₁@(I x₁ y₁) ⊂ i₂@(I x₂ y₂)
    | null i₂   = False
    | null i₁   = True
    | otherwise = x₁ > x₂ ∧ y₁ < y₂

(⊃) ∷ (Num α, Ord α) ⇒ I α → I α → Bool
(⊃) = flip (⊂)

(⊄) ∷ (Num α, Ord α) ⇒ I α → I α → Bool
a ⊄ b = not (a ⊂ b)

(⊅) ∷ (Num α, Ord α) ⇒ I α → I α → Bool
a ⊅ b = not (a ⊃ b)

infix 4 ⊂, ⊃, ⊄, ⊅

(⊆) ∷ (Num α, Ord α) ⇒ I α → I α → Bool
i₁ ⊆ i₂ | null i₁ ≡ null i₂ = True
        | otherwise         = i₁ ⊂ i₂

(⊇) ∷ (Num α, Ord α) ⇒ I α → I α → Bool
(⊇) = flip (⊆)

(⊈) ∷ (Num α, Ord α) ⇒ I α → I α → Bool
a ⊈ b = (a ≢ b) ∧ (a ⊄ b)

(⊉) ∷ (Num α, Ord α) ⇒ I α → I α → Bool
a ⊉ b = (a ≢ b) ∧ (a ⊅ b)

infix 4 ⊆, ⊇, ⊈, ⊉

--------------------------------------------------------------------------------

(∪) ∷ (Num α, Ord α) ⇒ I α → I α → I α
i₁@(I x₁ y₁) ∪ i₂@(I x₂ y₂)
    | null i₁   = i₂
    | null i₂   = i₁
    | otherwise = I (min x₁ x₂) (max y₁ y₂)

infixl 6 ∪

--------------------------------------------------------------------------------

instance (Num α, PartialOrd α) ⇒ Num (I α) where
    I x₁ y₁ + I x₂ y₂ = I (x₁ + x₂) (y₁ + y₂)
    I x₁ y₁ - I x₂ y₂ = I (x₁ - y₂) (y₁ - x₂)
    I x₁ y₁ * I x₂ y₂ = let t = (,) <$> minimumPO [x₁⋅x₂, x₁⋅y₂, y₁⋅x₂, y₁⋅y₂]
                                    <*> maximumPO [x₁⋅x₂, x₁⋅y₂, y₁⋅x₂, y₁⋅y₂]
                    in case t of
                         Just (x, y) → I x y
                         Nothing     → empty

    negate x = (-1) ⋅ x
    abs    (I x y) = I (abs    x) (abs    y)
    signum (I x y) = I (signum x) (signum y)

    fromInteger = singleton ∘ fromInteger

--------------------------------------------------------------------------------

minimumPO ∷ PartialOrd α ⇒ [α] → Maybe α
minimumPO []     = Nothing
minimumPO (x:xs) = foldM minPO x xs

maximumPO ∷ PartialOrd α ⇒ [α] → Maybe α
maximumPO []     = Nothing
maximumPO (x:xs) = foldM maxPO x xs
