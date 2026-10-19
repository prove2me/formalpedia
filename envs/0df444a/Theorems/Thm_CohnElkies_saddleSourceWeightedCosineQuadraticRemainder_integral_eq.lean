-- Prove2me | Theorems.Thm_CohnElkies_saddleSourceWeightedCosineQuadraticRemainder_integral_eq
-- name    : CohnElkies.saddleSourceWeightedCosineQuadraticRemainder_integral_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:58.09238+00:00
-- url     : https://prove2.me/theorems/8ced14e0-146c-45c3-90ce-656b0fb880f1
-- title:
--   CohnElkies.saddleSourceWeightedCosineQuadraticRemainder_integral_eq
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

theorem CohnElkies.saddleSourceWeightedCosineQuadraticRemainder_integral_eq
    (w : ℝ → ℝ) {b c : ℝ}
    (hbc : b ≤ c)
    (hw : ContinuousOn w (Icc b c))
    (u T : ℝ) :
    (∫ a in b..c,
      (w a : ℂ) * saddleSourceCosineQuadraticRemainder a u T) =
      (∫ a in b..c,
        (w a : ℂ) *
          (Complex.cos
            ((a : ℂ) *
              ((T : ℂ) + Complex.I * (u : ℂ))) - 1)) -
        (∫ a in b..c,
          (w a : ℂ) *
            ((Real.cosh (u * a) : ℂ) - 1)) +
        Complex.I *
          ((T * ∫ a in b..c,
            w a * a * Real.sinh (u * a) : ℝ) : ℂ) +
        ((T ^ 2 / 2 * ∫ a in b..c,
          w a * a ^ 2 * Real.cosh (u * a) : ℝ) : ℂ) := by sorry
