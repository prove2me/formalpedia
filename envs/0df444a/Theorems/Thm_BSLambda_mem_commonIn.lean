-- Prove2me | Theorems.Thm_BSLambda_mem_commonIn
-- name    : BSLambda.mem_commonIn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:45:37.30626+00:00
-- url     : https://prove2.me/theorems/c7144729-f2a3-41cb-ade8-9434b6bd6872
-- title:
--   BSLambda: mem common In
-- statement:
--   The BSLambda construction uses the mem common In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Tournament.lean#L138-L138
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Tournament.lean#L138-L138

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

theorem BSLambda.mem_commonIn : l ∈ commonIn Arc i j ↔ Arc l i ∧ Arc l j := by sorry
