-- Prove2me | Theorems.Thm_CohnElkies_saddleGaussian_weighted_integral_le_rescaled
-- name    : CohnElkies.saddleGaussian_weighted_integral_le_rescaled
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:59.395342+00:00
-- url     : https://prove2.me/theorems/644ded5c-2e8b-49f7-aeb8-0a38fced4817
-- title:
--   CohnElkies.saddleGaussian_weighted_integral_le_rescaled
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
open Filter Set MeasureTheory intervalIntegral
open scoped Topology

theorem CohnElkies.saddleGaussian_weighted_integral_le_rescaled
    {k : ℝ} (hk : 0 < k) :
    (∫ T : ℝ,
      saddleGaussianTailWeight T *
        Real.exp (-k * T ^ 2)) ≤
      2 * max (1 : ℝ)
          ((Real.sqrt (k / 6) ^ 3)⁻¹) *
        Real.sqrt (Real.pi / (k / 2)) := by sorry
