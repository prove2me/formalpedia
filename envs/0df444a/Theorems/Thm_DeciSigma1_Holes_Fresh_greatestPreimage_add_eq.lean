-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_greatestPreimage_add_eq
-- name    : DeciSigma1.Holes.Fresh.greatestPreimage_add_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:50:41.493439+00:00
-- url     : https://prove2.me/theorems/be9dd609-b879-479b-bf4c-5af3e6e7a62d
-- title:
--   Fresh: greatest Preimage add eq
-- statement:
--   If `n ≥ 1` and no junction lies strictly inside `(a, a + n)`, a retained cut with image
--   `a + n` that is not the right end of a site lies `n` letters after the greatest preimage of
--   `a`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/DeletionCoordinates.lean#L133-L143
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/DeletionCoordinates.lean#L133-L143

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

theorem DeciSigma1.Holes.Fresh.greatestPreimage_add_eq {a n p : ℕ} (hn : 0 < n)
    (hfree : ∀ J, IsJunction δ cs J → ¬ (a < J ∧ J < a + n)) (hp : Retained δ cs p)
    (hpr : ∀ c ∈ cs, p ≠ c + δ) (hk : retainedCount (sitePositions δ cs) p = a + n) :
    greatestPreimage (sitePositions δ cs) a + n = p := by sorry
