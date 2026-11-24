-- Prove2me | Theorems.Thm_BSLambda_LLL_active_flag_typeA
-- name    : BSLambda.LLL.active_flag_typeA
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:06:59.349602+00:00
-- url     : https://prove2.me/theorems/14ff793e-4ea1-4535-aa76-4b441c36575e
-- title:
--   LLL: active flag type A
-- statement:
--   The Type A flag built from a dominating centre is active with support `S`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L694-L703
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L694-L703

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

theorem BSLambda.LLL.active_flag_typeA {Arc : ι → ι → Bool} {S : Finset ι} (hS : S.card = 5) {h : ι}
    (hh : h ∈ S) (hdom : ∀ j ∈ S, j ≠ h → Arc h j = true) :
    ({ owner := h, top := none, bot := S.erase h } : Flag1 ι).Active Arc ∧
      ({ owner := h, top := none, bot := S.erase h } : Flag1 ι).supp = S := by sorry
