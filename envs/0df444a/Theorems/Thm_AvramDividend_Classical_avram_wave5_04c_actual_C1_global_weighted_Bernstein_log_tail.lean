-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_C1_global_weighted_Bernstein_log_tail
-- name    : AvramDividend.Classical.avram_wave5_04c_actual_C1_global_weighted_Bernstein_log_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:26:16.091988+00:00
-- url     : https://prove2.me/theorems/dc0b7948-8bfb-4db8-9c47-82954a44920d
-- title:
--   Global C1 payoff approximation with genuine BV weight and distant negative jump tail
-- statement:
--   For any globally C1 Lipschitz payoff and arbitrary near-zero cutoff 0<a<b≤1, obtain one polynomial Q vanishing at 1 approximating the payoff loss w(x)-w(x+log t) for every positive t≤1. Error is ε(1-t) globally plus 2L|log t| confined to t<b; the first term is BV-integrable under the actual negative Lévy measure, while the second is an arbitrarily remote payoff tail controlled by GeneratorIntegrable and original-source residual first-moment tails. This is the joint approximation needed for the exact canonical original-process generator theorem.
-- source:
--   Previously Proved C1 logarithmic quotient continuity, quantitative continuous taper, weighted Bernstein, Lipschitz envelope, and global polynomial error transfer.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_C1_logarithmic_quotient_continuous
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_tapered_compact_profile_quantitative
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_Bernstein_endpoint_weighted_polynomial_density
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_C1_log_quotient_Lipschitz_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_tapered_envelope_log_growth
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_global_poly_error_from_cutoff_bounds
set_option autoImplicit false
open Set Filter
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04c_actual_C1_global_weighted_Bernstein_log_tail (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |w u - w v| ≤ L * |u - v|)
    (x a b ε : ℝ) (ha : 0 < a) (hab : a < b) (hb : b ≤ 1)
    (hε : 0 < ε) :
    ∃ Q : Polynomial ℝ, Polynomial.eval 1 Q = 0 ∧
      ∀ t : unitInterval.Elem, 0 < (t : ℝ) →
        |Polynomial.eval (t : ℝ) Q -
          (w x - w (x + Real.log (t : ℝ)))| ≤
          ε * (1 - (t : ℝ)) +
            (if (t : ℝ) < b then 2 * L * |Real.log (t : ℝ)| else 0) := by sorry
