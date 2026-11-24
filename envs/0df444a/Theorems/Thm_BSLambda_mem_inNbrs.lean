-- Prove2me | Theorems.Thm_BSLambda_mem_inNbrs
-- name    : BSLambda.mem_inNbrs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:44:48.821814+00:00
-- url     : https://prove2.me/theorems/a5ae1eeb-8ec6-4680-829c-bbfd6db81660
-- title:
--   BSLambda: mem in Nbrs
-- statement:
--   The BSLambda construction uses the mem in Nbrs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Tournament.lean#L106-L106
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Tournament.lean#L106-L106

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

theorem BSLambda.mem_inNbrs : j ∈ inNbrs Arc i ↔ Arc j i := by sorry
