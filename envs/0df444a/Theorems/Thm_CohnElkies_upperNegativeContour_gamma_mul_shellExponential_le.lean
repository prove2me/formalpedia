-- Prove2me | Theorems.Thm_CohnElkies_upperNegativeContour_gamma_mul_shellExponential_le
-- name    : CohnElkies.upperNegativeContour_gamma_mul_shellExponential_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:57.456036+00:00
-- url     : https://prove2.me/theorems/9b0f77df-ff8b-4dc5-ae5e-0daef4477a6f
-- title:
--   CohnElkies.upperNegativeContour_gamma_mul_shellExponential_le
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
open scoped Topology BigOperators

theorem CohnElkies.upperNegativeContour_gamma_mul_shellExponential_le
    {ε ℓ : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hℓ : 0 < ℓ) (N : ℕ)
    (hN : 2 * (((N + 1 : ℕ) : ℝ)) ≤ ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hmargin : ∀ a ∈ Icc (shortCutoff ε) (shortEndpoint ε),
      0 ≤ shortMargin ε a)
    (s : ℝ) :
    ‖Complex.Gamma
        (((saddleTaylorContour N : ℂ) +
          (s : ℂ) * Complex.I) / 2) *
      Complex.exp
        ((ℓ : ℂ) * mellinShellPhase ε
          (Complex.I *
            (((saddleTaylorContour N : ℂ) +
              (s : ℂ) * Complex.I) - (ℓ : ℂ)) /
                (ℓ : ℂ)))‖ ≤
      Real.exp
        (ℓ * realHyperbolicShellPhase ε
          (saddleNegativeContourOrdinate ℓ N)) *
        ((Real.pi / Real.Gamma ((N : ℝ) + 3 / 2)) *
          Real.exp (2 * ε * Real.log 2) *
            Real.exp (-ε * Real.pi * |s|)) := by sorry
