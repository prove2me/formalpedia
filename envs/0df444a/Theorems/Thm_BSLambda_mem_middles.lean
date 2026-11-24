-- Prove2me | Theorems.Thm_BSLambda_mem_middles
-- name    : BSLambda.mem_middles
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:45:36.867143+00:00
-- url     : https://prove2.me/theorems/871545db-c5ba-45d1-8742-8fd215e3546e
-- title:
--   BSLambda: mem middles
-- statement:
--   The BSLambda construction uses the mem middles property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Tournament.lean#L140-L140
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Tournament.lean#L140-L140

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

theorem BSLambda.mem_middles : l ∈ middles Arc u v ↔ Arc u l ∧ Arc l v := by sorry
