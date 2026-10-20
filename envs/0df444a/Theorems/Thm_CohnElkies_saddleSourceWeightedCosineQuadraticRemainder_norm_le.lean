-- Prove2me | Theorems.Thm_CohnElkies_saddleSourceWeightedCosineQuadraticRemainder_norm_le
-- name    : CohnElkies.saddleSourceWeightedCosineQuadraticRemainder_norm_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:58.09238+00:00
-- url     : https://prove2.me/theorems/bc56fbc0-d03d-4bf3-9e9d-3e733c0c913d
-- title:
--   CohnElkies.saddleSourceWeightedCosineQuadraticRemainder_norm_le
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

theorem CohnElkies.saddleSourceWeightedCosineQuadraticRemainder_norm_le
    (w : ℝ → ℝ) {b c : ℝ}
    (hbc : b ≤ c)
    (hb : 0 ≤ b)
    (hw : ContinuousOn w (Icc b c))
    (hwnonneg : ∀ a ∈ Icc b c, 0 ≤ w a)
    (u T : ℝ) :
    ‖∫ a in b..c,
        (w a : ℂ) * saddleSourceCosineQuadraticRemainder a u T‖ ≤
      (|T| ^ 3 / 6) *
        ∫ a in b..c,
          w a * a ^ 3 * Real.cosh (u * a) := by sorry
