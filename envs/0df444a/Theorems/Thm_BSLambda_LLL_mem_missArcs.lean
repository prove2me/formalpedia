-- Prove2me | Theorems.Thm_BSLambda_LLL_mem_missArcs
-- name    : BSLambda.LLL.mem_missArcs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:59:45.921364+00:00
-- url     : https://prove2.me/theorems/387365c5-e559-4dfa-9c81-09e90c75106b
-- title:
--   LLL: mem miss Arcs
-- statement:
--   The LLL construction uses the mem miss Arcs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L834-L835
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L834-L835

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

theorem BSLambda.LLL.mem_missArcs : p ∈ missArcs Arc γ Z T ↔ p ∈ arcSet Arc T ∧ γ p.1 p.2 ∉ Z p.2 := by sorry
