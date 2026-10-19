-- Prove2me | Theorems.Thm_CohnElkies_saddleSource_weighted_tail_integral_le
-- name    : CohnElkies.saddleSource_weighted_tail_integral_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:57:00.023852+00:00
-- url     : https://prove2.me/theorems/879b9158-1ab5-4ebb-95a3-8ec5acac8bb2
-- title:
--   CohnElkies.saddleSource_weighted_tail_integral_le
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

theorem CohnElkies.saddleSource_weighted_tail_integral_le
    {F : ℝ → ℂ} {W : ℝ → ℝ} {C A R : ℝ}
    (hF : Integrable F)
    (hW : Integrable W)
    (hpoint : ∀ T ∈ saddleGaussianTailSet R,
      ‖F T‖ ≤ (C * A) * W T) :
    (∫ T : ℝ in saddleGaussianTailSet R, ‖F T‖) ≤
      C * A * (∫ T : ℝ in saddleGaussianTailSet R, W T) := by sorry
