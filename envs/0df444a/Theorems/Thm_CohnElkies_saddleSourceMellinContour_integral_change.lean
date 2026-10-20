-- Prove2me | Theorems.Thm_CohnElkies_saddleSourceMellinContour_integral_change
-- name    : CohnElkies.saddleSourceMellinContour_integral_change
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:57.456036+00:00
-- url     : https://prove2.me/theorems/7eb73cbb-27f6-4039-8355-20ea710e9a2b
-- title:
--   CohnElkies.saddleSourceMellinContour_integral_change
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
open scoped ContDiff FourierTransform Interval RealInnerProductSpace
  SchwartzMap Topology

theorem CohnElkies.saddleSourceMellinContour_integral_change
    {ℓ : ℝ} (hℓ : 0 < ℓ)
    (u : ℝ) (F : ℂ → ℂ) :
    (∫ t : ℝ,
      F (((ℓ * (1 + u) : ℝ) : ℂ) +
        (t : ℂ) * Complex.I)) =
      (ℓ : ℂ) *
        (∫ T : ℝ,
          F (saddleSourceMellinContour ℓ u T)) := by sorry
