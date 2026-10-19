-- Prove2me | Theorems.Thm_CohnElkies_minusSaddleProfile_re_neg_at_sourceSaddle_of_gaussian_error
-- name    : CohnElkies.minusSaddleProfile_re_neg_at_sourceSaddle_of_gaussian_error
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:57:02.654547+00:00
-- url     : https://prove2.me/theorems/ddb01b31-6076-4bdd-9d46-e33c85453526
-- title:
--   CohnElkies.minusSaddleProfile_re_neg_at_sourceSaddle_of_gaussian_error
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
open scoped FourierTransform SchwartzMap Topology

theorem CohnElkies.minusSaddleProfile_re_neg_at_sourceSaddle_of_gaussian_error
    {ε : ℝ} {d : ℕ} {u : ℝ}
    (hε : 0 < ε) (hd : 0 < d) (hu : -1 < u)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hV : 0 < saddleSourceGaussianVariance ε ((d : ℝ) / 2) u)
    (herror :
      ‖(∫ T : ℝ,
          saddleSourceCenteredMinusIntegrand ε ((d : ℝ) / 2) u
            (saddleLogRadius ε d u) T) -
        (∫ T : ℝ,
          saddleSourceGaussianMinusIntegrand ε ((d : ℝ) / 2) u T)‖ <
        -(∫ T : ℝ,
          saddleSourceGaussianMinusIntegrand ε ((d : ℝ) / 2) u T).re) :
    (minusSaddleProfile ε ((d : ℝ) / 2)
      (Real.exp (saddleLogRadius ε d u))).re < 0 := by sorry
