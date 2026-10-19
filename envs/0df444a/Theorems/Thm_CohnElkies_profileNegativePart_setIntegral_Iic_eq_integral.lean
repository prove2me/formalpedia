-- Prove2me | Theorems.Thm_CohnElkies_profileNegativePart_setIntegral_Iic_eq_integral
-- name    : CohnElkies.profileNegativePart_setIntegral_Iic_eq_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:52.959427+00:00
-- url     : https://prove2.me/theorems/f93febf5-ce3f-434c-9400-cfbfa0de96e9
-- title:
--   CohnElkies.profileNegativePart_setIntegral_Iic_eq_integral
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | SpherePacking | external Lean 4.33.1 validation; bundle SHA256 ecca43e9570778e44777003bd5984d4ec94cd395fce5324c69b88ac50ad79ed2

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology

theorem CohnElkies.profileNegativePart_setIntegral_Iic_eq_integral {φ : ℝ → ℝ}
    (hsign : ∀ v : ℝ, 0 ≤ v → 0 ≤ φ v) :
    (∫ v in Iic (0 : ℝ), profileNegativePart φ v) =
      ∫ v : ℝ, profileNegativePart φ v := by sorry
