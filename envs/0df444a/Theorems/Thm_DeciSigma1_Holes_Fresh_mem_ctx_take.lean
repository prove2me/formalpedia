-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_mem_ctx_take
-- name    : DeciSigma1.Holes.Fresh.mem_ctx_take
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:04:36.28575+00:00
-- url     : https://prove2.me/theorems/2dbe9498-e0d9-403a-b618-e978aeccc6fd
-- title:
--   Fresh: mem ctx take
-- statement:
--   The Fresh construction uses the mem ctx take property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/DeletionCoordinates.lean#L388-L391
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/DeletionCoordinates.lean#L388-L391

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

theorem DeciSigma1.Holes.Fresh.mem_ctx_take {W : Fin k → List α} {t : ℕ} {x : List α} {e p : ℕ} (hep : e ≤ p)
    (hp : p ≤ x.length) : e ∈ contextAnchors W t (x.take p) ↔ e ∈ contextAnchors W t x := by sorry
