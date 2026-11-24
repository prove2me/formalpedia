-- Prove2me | Theorems.Thm_BSLambda_LLL_active_flag_typeB
-- name    : BSLambda.LLL.active_flag_typeB
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:07:08.024123+00:00
-- url     : https://prove2.me/theorems/3479bd79-ac5a-42d2-9247-12571bb2ae71
-- title:
--   LLL: active flag type B
-- statement:
--   The Type B flag built from a centre `h` and the unique `a` beating it is active with
--   support `S`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L708-L723
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L708-L723

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

theorem BSLambda.LLL.active_flag_typeB {Arc : ι → ι → Bool} {S : Finset ι} (hS : S.card = 5) {h a : ι}
    (hh : h ∈ S) (ha : a ∈ S) (hah : a ≠ h) (harc : Arc a h = true)
    (hdom : ∀ j ∈ S, j ≠ h → j ≠ a → Arc h j = true ∧ Arc a j = true) :
    ({ owner := h, top := some a, bot := (S.erase h).erase a } : Flag1 ι).Active Arc ∧
      ({ owner := h, top := some a, bot := (S.erase h).erase a } : Flag1 ι).supp = S := by sorry
