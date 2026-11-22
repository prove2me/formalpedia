-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_pred_not_mem_sitePositions
-- name    : DeciSigma1.Holes.Fresh.pred_not_mem_sitePositions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:04:18.513869+00:00
-- url     : https://prove2.me/theorems/147bd199-2c49-438f-b337-ec0081e174c9
-- title:
--   Fresh: pred not mem site Positions
-- statement:
--   A retained cut that is not the right end of a site does not end a deleted interval.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/DeletionCoordinates.lean#L77-L84
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/DeletionCoordinates.lean#L77-L84

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

theorem DeciSigma1.Holes.Fresh.pred_not_mem_sitePositions {p : ℕ} (hp : Retained δ cs p) (hpr : ∀ c ∈ cs, p ≠ c + δ) :
    p = 0 ∨ p - 1 ∉ sitePositions δ cs := by sorry
