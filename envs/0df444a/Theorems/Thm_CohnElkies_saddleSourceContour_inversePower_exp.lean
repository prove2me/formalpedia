-- Prove2me | Theorems.Thm_CohnElkies_saddleSourceContour_inversePower_exp
-- name    : CohnElkies.saddleSourceContour_inversePower_exp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:57.456036+00:00
-- url     : https://prove2.me/theorems/3d8b6682-20bc-4be0-9721-65ba8d41c130
-- title:
--   CohnElkies.saddleSourceContour_inversePower_exp
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

theorem CohnElkies.saddleSourceContour_inversePower_exp
    (ℓ u v T : ℝ) :
    saddleMellinInversePower (Real.exp v)
        (saddleSourceMellinContour ℓ u T) =
      ((Real.exp (-(ℓ * (1 + u) * v)) : ℝ) : ℂ) *
        Complex.exp
          (Complex.I * ((ℓ * T * v : ℝ) : ℂ)) := by sorry
