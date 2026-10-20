-- Prove2me | Theorems.Thm_CohnElkies_saddleSourceContour_gamma_norm
-- name    : CohnElkies.saddleSourceContour_gamma_norm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:57.456036+00:00
-- url     : https://prove2.me/theorems/ecf370e7-8641-4500-b63b-5cc80fc9a77a
-- title:
--   CohnElkies.saddleSourceContour_gamma_norm
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

theorem CohnElkies.saddleSourceContour_gamma_norm
    {ℓ u : ℝ} (hℓ : 0 < ℓ) (hu : -1 < u)
    (T : ℝ) :
    ‖Complex.Gamma
      (saddleSourceMellinContour ℓ u T / 2)‖ =
      Real.Gamma (ℓ * (1 + u) / 2) *
        Real.exp (-upperGammaDamping ℓ (1 + u) T) := by sorry
