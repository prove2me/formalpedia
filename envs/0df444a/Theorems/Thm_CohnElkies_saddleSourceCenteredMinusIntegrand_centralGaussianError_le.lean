-- Prove2me | Theorems.Thm_CohnElkies_saddleSourceCenteredMinusIntegrand_centralGaussianError_le
-- name    : CohnElkies.saddleSourceCenteredMinusIntegrand_centralGaussianError_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:58.736036+00:00
-- url     : https://prove2.me/theorems/dbe42c3d-f72a-46c7-9385-4a3a3c70109d
-- title:
--   CohnElkies.saddleSourceCenteredMinusIntegrand_centralGaussianError_le
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

theorem CohnElkies.saddleSourceCenteredMinusIntegrand_centralGaussianError_le
    {ε ℓ u R q p : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ) (hu : -1 < u)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hmargin : ∀ a ∈ Icc (shortCutoff ε) (shortEndpoint ε),
      0 ≤ shortMargin ε a)
    (hV : 0 < saddleSourceGaussianVariance ε ℓ u)
    (hR : 0 ≤ R) (hq : 0 ≤ q) (hqone : q ≤ 1)
    (hp : 0 ≤ p)
    (hcubic : ∀ T : ℝ, |T| ≤ R →
      (ℓ * upperSaddleThirdMoment ε ℓ (u - 1) / 6) *
        |T| ^ 3 ≤ q)
    (hpoly : ∀ T : ℝ, |T| ≤ R →
      ‖minusPolynomial ε
          ((T : ℂ) + Complex.I * (u : ℂ)) -
        minusPolynomial ε (Complex.I * (u : ℂ))‖ ≤
          p * ‖minusPolynomial ε (Complex.I * (u : ℂ))‖) :
    ‖∫ T : ℝ in Icc (-R) R,
        (saddleSourceCenteredMinusIntegrand ε ℓ u
          (saddleSourceStationaryLogRadius ε ℓ u) T -
            saddleSourceGaussianMinusIntegrand ε ℓ u T)‖ ≤
      (2 * q + (1 + 2 * q) * p) *
        ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ *
          ∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T := by sorry
