-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_take_drop_deleteSites
-- name    : DeciSigma1.Holes.Fresh.take_drop_deleteSites
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:47:20.033312+00:00
-- url     : https://prove2.me/theorems/45c8e2df-9312-407f-9c61-1c09396f503b
-- title:
--   Fresh: take drop delete Sites
-- statement:
--   If no junction lies strictly inside `(a, a + n)`, the `n` letters of the edited text read from
--   `a` are the `n` letters of the original text read from the greatest preimage of `a`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/DeletionCoordinates.lean#L124-L128
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/DeletionCoordinates.lean#L124-L128

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Deletion
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_DeletionCoordinates
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers DeciSigma1.Words
open Finset
variable {δ : ℕ} {cs : Finset ℕ}

theorem DeciSigma1.Holes.Fresh.take_drop_deleteSites {α : Type} (x : List α) {a n : ℕ}
    (hfree : ∀ J, IsJunction δ cs J → ¬ (a < J ∧ J < a + n)) :
    ((deletePositions x (sitePositions δ cs)).drop a).take n =
      (x.drop (greatestPreimage (sitePositions δ cs) a)).take n := by sorry
