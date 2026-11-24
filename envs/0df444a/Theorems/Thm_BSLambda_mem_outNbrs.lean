-- Prove2me | Theorems.Thm_BSLambda_mem_outNbrs
-- name    : BSLambda.mem_outNbrs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:44:46.197269+00:00
-- url     : https://prove2.me/theorems/bc916ab4-8c12-449f-ae0e-62b6f5ee444c
-- title:
--   BSLambda: mem out Nbrs
-- statement:
--   The BSLambda construction uses the mem out Nbrs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Tournament.lean#L104-L104
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Tournament.lean#L104-L104

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
variable {Arc : ι → ι → Bool} {i j : ι}

theorem BSLambda.mem_outNbrs : j ∈ outNbrs Arc i ↔ Arc i j := by sorry
