-- Prove2me | Theorems.Thm_CohnElkies_saddleSourceCenteredEnvelope_stationary_gaussian_error_le
-- name    : CohnElkies.saddleSourceCenteredEnvelope_stationary_gaussian_error_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:58.736036+00:00
-- url     : https://prove2.me/theorems/a8bd6d63-1c1e-415d-bed0-531d6e0549fc
-- title:
--   CohnElkies.saddleSourceCenteredEnvelope_stationary_gaussian_error_le
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

theorem CohnElkies.saddleSourceCenteredEnvelope_stationary_gaussian_error_le
    {ε ℓ u : ℝ}
    (hε : 0 < ε)
    (hℓ : 0 < ℓ)
    (hu : -1 < u)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hmargin : ∀ a ∈ Icc (shortCutoff ε) (shortEndpoint ε),
      0 ≤ shortMargin ε a)
    (T : ℝ)
    (hsmall :
      (ℓ * upperSaddleThirdMoment ε ℓ (u - 1) / 6) *
        |T| ^ 3 ≤ 1) :
    ‖saddleSourceCenteredEnvelope ε ℓ u
        (saddleSourceStationaryLogRadius ε ℓ u) T -
      (saddleSourceGaussianKernel ε ℓ u T : ℂ)‖ ≤
      2 * saddleSourceGaussianKernel ε ℓ u T *
        ((ℓ * upperSaddleThirdMoment ε ℓ (u - 1) / 6) *
          |T| ^ 3) := by sorry
