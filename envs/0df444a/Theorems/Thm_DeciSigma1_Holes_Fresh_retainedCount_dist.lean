-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_retainedCount_dist
-- name    : DeciSigma1.Holes.Fresh.retainedCount_dist
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:50:32.627292+00:00
-- url     : https://prove2.me/theorems/6eda0b2c-30ca-46fa-83f7-1f714b164eaf
-- title:
--   Fresh: retained Count dist
-- statement:
--   The cut map is a shift on a stretch without sites.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/DeletionCoordinates.lean#L95-L104
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/DeletionCoordinates.lean#L95-L104

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

theorem DeciSigma1.Holes.Fresh.retainedCount_dist {p q : ℕ} (hp : Retained δ cs p) (hpq : p ≤ q)
    (hno : ∀ c ∈ cs, ¬ (p ≤ c ∧ c < q)) :
    retainedCount (sitePositions δ cs) q = retainedCount (sitePositions δ cs) p + (q - p) := by sorry
