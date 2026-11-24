-- Prove2me | Theorems.Thm_BSLambda_mem_commonOut
-- name    : BSLambda.mem_commonOut
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:45:29.398789+00:00
-- url     : https://prove2.me/theorems/9e9492b4-a19c-45b6-8e45-47f2ae455e8c
-- title:
--   BSLambda: mem common Out
-- statement:
--   The BSLambda construction uses the mem common Out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Tournament.lean#L136-L136
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Tournament.lean#L136-L136

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Fintype.Card
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Tournament
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open Finset
variable {ι : Type*}
variable [Fintype ι]
variable [DecidableEq ι]
variable {Arc : ι → ι → Bool} {i j l u v : ι}

theorem BSLambda.mem_commonOut : l ∈ commonOut Arc i j ↔ Arc i l ∧ Arc j l := by sorry
