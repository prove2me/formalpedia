-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_retainedCount_site_right
-- name    : DeciSigma1.Holes.Fresh.retainedCount_site_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:50:32.832452+00:00
-- url     : https://prove2.me/theorems/1c0f4c7d-624a-4082-a12f-2a22377b3af1
-- title:
--   Fresh: retained Count site right
-- statement:
--   The two ends of a site have the same image.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/DeletionCoordinates.lean#L107-L109
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/DeletionCoordinates.lean#L107-L109

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

theorem DeciSigma1.Holes.Fresh.retainedCount_site_right {c : ℕ} (hc : c ∈ cs) :
    retainedCount (sitePositions δ cs) (c + δ) = retainedCount (sitePositions δ cs) c := by sorry
