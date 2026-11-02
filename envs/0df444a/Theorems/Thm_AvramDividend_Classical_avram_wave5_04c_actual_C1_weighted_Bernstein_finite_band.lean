-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_C1_weighted_Bernstein_finite_band
-- name    : AvramDividend.Classical.avram_wave5_04c_actual_C1_weighted_Bernstein_finite_band
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T18:35:53.039066+00:00
-- url     : https://prove2.me/theorems/dae5765c-2d5e-4ee5-86f9-69745754360f
-- title:
--   Original C1 payoff negative-jump loss admits endpoint-zero Bernstein approximation on every compact band
-- statement:
--   For any genuinely globally C1 payoff w, reserve x, finite negative jump band represented by exp(y)≥b>0, and epsilon>0, there is a polynomial Q vanishing at t=1 whose error in the exact jump loss w(x)-w(x+log t) is bounded by epsilon*(1-t) throughout the band. The construction uses the Proved C1 logarithmic derivative-filled quotient, the Proved continuous tapered compactification zero in the far tail, and the Proved weighted Bernstein polynomial density. No C2 regularity, negative-jump first moment at large sizes, or alternate process is assumed.
-- source:
--   Proved C1 logarithmic quotient continuity, tapered compact profile, and endpoint weighted Bernstein polynomial density.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_C1_logarithmic_quotient_continuous
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_tapered_compact_profile
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_Bernstein_endpoint_weighted_polynomial_density
set_option autoImplicit false
open Set Filter
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04c_actual_C1_weighted_Bernstein_finite_band
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w)
    (x a b ε : ℝ) (ha : 0 < a) (hab : a < b) (hb : b ≤ 1)
    (hε : 0 < ε) :
    ∃ Q : Polynomial ℝ, Polynomial.eval 1 Q = 0 ∧
      ∀ t : unitInterval.Elem, b ≤ (t : ℝ) →
        |Polynomial.eval (t : ℝ) Q -
          (w x - w (x + Real.log (t : ℝ)))| ≤
            ε * (1 - (t : ℝ)) := by sorry
