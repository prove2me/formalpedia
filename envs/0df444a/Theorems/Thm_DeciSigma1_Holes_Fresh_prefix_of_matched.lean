-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_prefix_of_matched
-- name    : DeciSigma1.Holes.Fresh.prefix_of_matched
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:04:24.046625+00:00
-- url     : https://prove2.me/theorems/3209497a-e70f-4ec2-9431-5b71079f8b54
-- title:
--   Fresh: prefix of matched
-- statement:
--   If the junctions strictly inside a comparison of edited texts correspond on both sides, and
--   every site deletes the same text `F`, then reinserting `F` on both sides gives a comparison of
--   original texts, read from the greatest preimages of the cuts.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/DeletionCoordinates.lean#L162-L252
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/DeletionCoordinates.lean#L162-L252

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Deletion
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_DeletionCoordinates
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers DeciSigma1.Words
open Finset
variable {α : Type} {δ : ℕ}

theorem DeciSigma1.Holes.Fresh.prefix_of_matched (hδ : 0 < δ) {F x y : List α} {cx cy : Finset ℕ}
    (hsx : StrictlySeparated δ cx) (hsy : StrictlySeparated δ cy)
    (hx : ∀ c ∈ cx, c + δ < x.length ∧ (x.drop c).take δ = F)
    (hy : ∀ c ∈ cy, c + δ < y.length ∧ (y.drop c).take δ = F) :
    ∀ L a b, (deletePositions y (sitePositions δ cy)).length = b + L →
      (deletePositions y (sitePositions δ cy)).drop b <+:
        (deletePositions x (sitePositions δ cx)).drop a →
      (∀ d, 0 < d → d < L → (IsJunction δ cx (a + d) ↔ IsJunction δ cy (b + d))) →
      y.drop (greatestPreimage (sitePositions δ cy) b) <+:
          x.drop (greatestPreimage (sitePositions δ cx) a) := by sorry
