-- Prove2me | Theorems.Thm_BSLambda_LLL_mem_discSet
-- name    : BSLambda.LLL.mem_discSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:59:44.345351+00:00
-- url     : https://prove2.me/theorems/04788915-b877-49c6-8b03-1b72aef3e6c4
-- title:
--   LLL: mem disc Set
-- statement:
--   The LLL construction uses the mem disc Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L839-L840
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L839-L840

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
variable {Arc : ι → ι → Bool} {γ : ι → ι → Fin r} {Z : ι → Finset (Fin r)} {T : Finset ι}
  {p : ι × ι}
omit [DecidableEq ι]

theorem BSLambda.LLL.mem_discSet {h j : ι} : j ∈ discSet γ Z T h ↔ j ∈ T ∧ ¬ (Z j ⊆ {γ h j}) := by sorry
