-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_mem_contextAnchors_of_mem_anchors_of_lt_length
-- name    : DeciSigma1.Holes.Fresh.mem_contextAnchors_of_mem_anchors_of_lt_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:50:39.882837+00:00
-- url     : https://prove2.me/theorems/e74e7b33-2840-4eaa-bfdd-34fa19ae07b8
-- title:
--   Fresh: mem context Anchors of mem anchors of lt length
-- statement:
--   The Fresh construction uses the mem context Anchors of mem anchors of lt length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/DeletionCoordinates.lean#L262-L267
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/DeletionCoordinates.lean#L262-L267

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Deletion
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_DeletionCoordinates
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers DeciSigma1.Words
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ}

theorem DeciSigma1.Holes.Fresh.mem_contextAnchors_of_mem_anchors_of_lt_length {W : Fin k → List α} {t : ℕ} {l : Fin k}
    {p : ℕ}
    (hp : p ∈ anchors W t l) (hlt : p < (W l).length) : p ∈ contextAnchors W t (W l) := by sorry
