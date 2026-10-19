-- Prove2me | Theorems.Thm_CohnElkies_eventually_saddleSourceFirstBranch_fullGaussianErrors
-- name    : CohnElkies.eventually_saddleSourceFirstBranch_fullGaussianErrors
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:57:00.023852+00:00
-- url     : https://prove2.me/theorems/881a020d-3fb6-420e-9384-242b07edcb38
-- title:
--   CohnElkies.eventually_saddleSourceFirstBranch_fullGaussianErrors
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

theorem CohnElkies.eventually_saddleSourceFirstBranch_fullGaussianErrors :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ᶠ ℓ : ℝ in atTop,
        ∀ u : ℝ, -1 < u → u ≤ 1 + ε / 2 →
          Real.log ℓ / 4 ≤ ℓ * (1 + u) →
            (‖(∫ T : ℝ,
                saddleSourceCenteredPlusIntegrand ε ℓ u
                  (saddleSourceStationaryLogRadius ε ℓ u) T) -
              (∫ T : ℝ,
                saddleSourceGaussianPlusIntegrand ε ℓ u T)‖ <
              ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ *
                (∫ T : ℝ,
                  saddleSourceGaussianKernel ε ℓ u T)) ∧
            (1 + ε / 4 ≤ u →
              ‖(∫ T : ℝ,
                  saddleSourceCenteredMinusIntegrand ε ℓ u
                    (saddleSourceStationaryLogRadius ε ℓ u) T) -
                (∫ T : ℝ,
                  saddleSourceGaussianMinusIntegrand ε ℓ u T)‖ <
                ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ *
                  (∫ T : ℝ,
                    saddleSourceGaussianKernel ε ℓ u T)) := by sorry
