-- Prove2me | Theorems.Thm_CohnElkies_saddleSourceContour_shellExponential_norm
-- name    : CohnElkies.saddleSourceContour_shellExponential_norm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:57.456036+00:00
-- url     : https://prove2.me/theorems/ff2d168a-3277-4e25-a9a9-2e59b8bafe6b
-- title:
--   CohnElkies.saddleSourceContour_shellExponential_norm
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

theorem CohnElkies.saddleSourceContour_shellExponential_norm
    {ε ℓ u : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (T : ℝ) :
    ‖Complex.exp
      ((ℓ : ℂ) * mellinShellPhase ε
        (Complex.I *
          (saddleSourceMellinContour ℓ u T - (ℓ : ℂ)) /
            (ℓ : ℂ)))‖ =
      Real.exp (ℓ * realHyperbolicShellPhase ε u) *
        Real.exp
          (-(positiveShellDamping ε ℓ (u - 1) T -
            upperShortShellDamping ε ℓ (u - 1) T)) := by sorry
