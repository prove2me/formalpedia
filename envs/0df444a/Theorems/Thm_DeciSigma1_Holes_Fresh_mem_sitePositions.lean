-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_mem_sitePositions
-- name    : DeciSigma1.Holes.Fresh.mem_sitePositions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:43:09.352735+00:00
-- url     : https://prove2.me/theorems/dd078348-5ed8-4dae-8dab-11b08f5ad9ec
-- title:
--   Fresh: mem site Positions
-- statement:
--   The Fresh construction uses the mem site Positions property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L258-L259
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L258-L259

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Deletion
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers DeciSigma1.Words
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ}
variable {W : Fin k → List α}
variable {δ : ℕ} {cs : Finset ℕ}

theorem DeciSigma1.Holes.Fresh.mem_sitePositions {p : ℕ} : p ∈ sitePositions δ cs ↔ ∃ c ∈ cs, c ≤ p ∧ p < c + δ := by sorry
