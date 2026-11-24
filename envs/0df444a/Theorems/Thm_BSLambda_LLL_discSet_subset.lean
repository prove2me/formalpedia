-- Prove2me | Theorems.Thm_BSLambda_LLL_discSet_subset
-- name    : BSLambda.LLL.discSet_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:07:18.826803+00:00
-- url     : https://prove2.me/theorems/0266e467-f4be-431a-a4f0-ee3700108f4a
-- title:
--   LLL: disc Set subset
-- statement:
--   The LLL construction uses the disc Set subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L846-L846
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L846-L846

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

theorem BSLambda.LLL.discSet_subset {h : ι} : discSet γ Z T h ⊆ T := by sorry
