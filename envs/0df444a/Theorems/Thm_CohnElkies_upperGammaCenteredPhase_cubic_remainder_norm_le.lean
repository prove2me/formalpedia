-- Prove2me | Theorems.Thm_CohnElkies_upperGammaCenteredPhase_cubic_remainder_norm_le
-- name    : CohnElkies.upperGammaCenteredPhase_cubic_remainder_norm_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:58.09238+00:00
-- url     : https://prove2.me/theorems/220ca3ff-d91f-4542-b4fe-e2cadf58382c
-- title:
--   CohnElkies.upperGammaCenteredPhase_cubic_remainder_norm_le
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

theorem CohnElkies.upperGammaCenteredPhase_cubic_remainder_norm_le
    {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η)
    (T : ℝ) :
    ‖upperGammaCenteredPhase ℓ η T +
        ((ℓ * upperGammaVariance ℓ η / 2 * T ^ 2 : ℝ) : ℂ)‖ ≤
      (ℓ * upperGammaThirdMoment ℓ η / 6) * |T| ^ 3 := by sorry
