-- Prove2me | Theorems.Thm_CohnElkies_upperGammaCubicRemainderKernel_norm_le
-- name    : CohnElkies.upperGammaCubicRemainderKernel_norm_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:58.09238+00:00
-- url     : https://prove2.me/theorems/42de2831-4ceb-48e2-8c74-2dea81e43889
-- title:
--   CohnElkies.upperGammaCubicRemainderKernel_norm_le
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

theorem CohnElkies.upperGammaCubicRemainderKernel_norm_le
    {ℓ η a : ℝ} (hℓ : 0 < ℓ) (ha : 0 < a)
    (T : ℝ) :
    ‖upperGammaCubicRemainderKernel ℓ η T a‖ ≤
      (|T| ^ 3 / 6) *
        (a ^ 3 * upperGammaMeasureDensity ℓ η a) := by sorry
