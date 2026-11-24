-- Prove2me | Theorems.Thm_BSLambda_LLL_mem_arcSet
-- name    : BSLambda.LLL.mem_arcSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:59:23.08659+00:00
-- url     : https://prove2.me/theorems/0a8f744b-1186-4934-8fdf-9963dce635eb
-- title:
--   LLL: mem arc Set
-- statement:
--   The LLL construction uses the mem arc Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L102-L103
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L102-L103

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Asymmetric
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.LLL
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ}
omit [Fintype ι]
variable {Arc : ι → ι → Bool} {T : Finset ι} {p : ι × ι}
omit [DecidableEq ι]

theorem BSLambda.LLL.mem_arcSet : p ∈ arcSet Arc T ↔ (p.1 ∈ T ∧ p.2 ∈ T ∧ p.1 ≠ p.2) ∧ Arc p.1 p.2 := by sorry
