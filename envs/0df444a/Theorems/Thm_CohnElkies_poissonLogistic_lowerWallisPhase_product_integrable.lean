-- Prove2me | Theorems.Thm_CohnElkies_poissonLogistic_lowerWallisPhase_product_integrable
-- name    : CohnElkies.poissonLogistic_lowerWallisPhase_product_integrable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:54.348956+00:00
-- url     : https://prove2.me/theorems/9de98f28-5673-43a5-9e4d-e6f32c7d7bf0
-- title:
--   CohnElkies.poissonLogistic_lowerWallisPhase_product_integrable
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
open scoped Interval Topology

theorem CohnElkies.poissonLogistic_lowerWallisPhase_product_integrable :
    Integrable
      (fun p : ℝ × ℝ =>
        poissonLogisticDensity p.1 *
          lowerWallisPhaseKernel p.1 p.2)
      (volume.prod (volume.restrict (Ioi 0))) := by sorry
