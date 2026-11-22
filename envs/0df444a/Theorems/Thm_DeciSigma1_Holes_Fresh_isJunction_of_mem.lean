-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_isJunction_of_mem
-- name    : DeciSigma1.Holes.Fresh.isJunction_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:55:16.095+00:00
-- url     : https://prove2.me/theorems/7a915851-3c3c-4bc5-ab4f-89dfbf1b06d6
-- title:
--   Fresh: is Junction of mem
-- statement:
--   The image of a deleted position is a junction.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/DeletionCoordinates.lean#L87-L92
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/DeletionCoordinates.lean#L87-L92

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

theorem DeciSigma1.Holes.Fresh.isJunction_of_mem {p : ℕ} (hp : p ∈ sitePositions δ cs) :
    IsJunction δ cs (retainedCount (sitePositions δ cs) p) := by sorry
