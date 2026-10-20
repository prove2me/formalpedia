-- Prove2me | Theorems.Thm_CohnElkies_upperGammaCenteredPhase_add_quadratic_eq_integral
-- name    : CohnElkies.upperGammaCenteredPhase_add_quadratic_eq_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:58.09238+00:00
-- url     : https://prove2.me/theorems/8c12dd14-f32c-410d-9558-78c8c3e2968f
-- title:
--   CohnElkies.upperGammaCenteredPhase_add_quadratic_eq_integral
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
open scoped Topology

theorem CohnElkies.upperGammaCenteredPhase_add_quadratic_eq_integral
    {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η)
    (T : ℝ) :
    upperGammaCenteredPhase ℓ η T +
        ((ℓ * upperGammaVariance ℓ η / 2 * T ^ 2 : ℝ) : ℂ) =
      ∫ a : ℝ in Ioi 0,
        upperGammaCubicRemainderKernel ℓ η T a := by sorry
