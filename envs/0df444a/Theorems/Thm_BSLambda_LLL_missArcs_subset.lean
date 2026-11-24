-- Prove2me | Theorems.Thm_BSLambda_LLL_missArcs_subset
-- name    : BSLambda.LLL.missArcs_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:07:16.738532+00:00
-- url     : https://prove2.me/theorems/072dfccd-3000-40f8-8fab-8e83673e6f51
-- title:
--   LLL: miss Arcs subset
-- statement:
--   The LLL construction uses the miss Arcs subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L843-L843
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L843-L843

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

theorem BSLambda.LLL.missArcs_subset : missArcs Arc γ Z T ⊆ arcSet Arc T := by sorry
