-- Prove2me | Theorems.Thm_BSLambda_LLL_missSet_subset_missSet
-- name    : BSLambda.LLL.missSet_subset_missSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:59:44.131316+00:00
-- url     : https://prove2.me/theorems/7b7d63cc-31f4-46f8-b667-50d857456d36
-- title:
--   LLL: miss Set subset miss Set
-- statement:
--   The LLL construction uses the miss Set subset miss Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L176-L177
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L176-L177

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
omit [Fintype ι] [DecidableEq ι]
variable {Arc : ι → ι → Bool} {γ γ' : ι → ι → Fin r} {Z : ι → Finset (Fin r)}
  {T T' S : Finset ι} {i j : ι}

theorem BSLambda.LLL.missSet_subset_missSet (hT : T ⊆ T') : missSet Arc γ Z T i ⊆ missSet Arc γ Z T' i := by sorry
