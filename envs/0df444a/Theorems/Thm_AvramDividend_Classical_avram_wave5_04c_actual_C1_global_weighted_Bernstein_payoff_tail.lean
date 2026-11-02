-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_C1_global_weighted_Bernstein_payoff_tail
-- name    : AvramDividend.Classical.avram_wave5_04c_actual_C1_global_weighted_Bernstein_payoff_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:32:07.77909+00:00
-- url     : https://prove2.me/theorems/f0589867-5639-4b69-9a7c-6ce344e15f9a
-- title:
--   Global C1 polynomial approximation with signed-payoff-integrable negative Lévy tail
-- statement:
--   For every globally C1 payoff, produce an endpoint-zero polynomial Q whose error over all positive t∈[0,1] is bounded by ε(1-t) plus twice the absolute genuine payoff increment only for t<b. Crucially, this does NOT bound large jumps by |log t|, which would impose a false global first moment. The second term integrates on the original Lévy measure because GeneratorIntegrable gives L1 integrability of the signed payoff increment. The same estimate under the original BV source is dominated by Lipschitz and normalized residual tail control.
-- source:
--   Quantitative taper and weighted Bernstein with the exact endpoint-filled C1 logarithmic chord relation.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_C1_logarithmic_quotient_continuous
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_tapered_compact_profile_quantitative
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_Bernstein_endpoint_weighted_polynomial_density
set_option autoImplicit false
open Set Filter
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04c_actual_C1_global_weighted_Bernstein_payoff_tail (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w)
    (x a b ε : ℝ) (ha : 0 < a) (hab : a < b) (hb : b ≤ 1)
    (hε : 0 < ε) :
    ∃ Q : Polynomial ℝ, Polynomial.eval 1 Q = 0 ∧
      ∀ t : unitInterval.Elem, 0 < (t : ℝ) →
        |Polynomial.eval (t : ℝ) Q -
          (w x - w (x + Real.log (t : ℝ)))| ≤
          ε * (1 - (t : ℝ)) +
            (if (t : ℝ) < b
              then 2 * |w x - w (x + Real.log (t : ℝ))| else 0) := by sorry
