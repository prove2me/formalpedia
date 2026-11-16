-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_restricted_discounted_Stieltjes_cash_real_lower
-- name    : AvramDividend.Classical.avram_bvb_obstruction_restricted_discounted_Stieltjes_cash_real_lower
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:49:28.700226+00:00
-- url     : https://prove2.me/theorems/7efc54fc-a4dd-49f9-b0cf-ef341a818405
-- title:
--   Finite restricted real discounted Stieltjes cash exceeds terminal discount times eight-hundredth positive interval mass
-- statement:
--   For any real-time dividend measure μ, a payment domain A containing (0,2/25], and exact μ mass 2/25 on that interval, if the discounted integral over A is finite, then its real value is at least (2/25) exp(−1/10). This directly gives the original stopped strict dividend prefix lower bound on the positive-probability zero-barrier nojump path.
-- source:
--   Proved general discounted Stieltjes lintegral lower bound at T=2/25; monotonicity under inclusion A; exact finite ENNReal-to-real monotonicity; exp(−1/10)≤exp(−2/25). All integrals retain original real-time dividend measure.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_discounted_Stieltjes_lintegral_lower_mass
open MeasureTheory Set Real
open scoped ENNReal

theorem AvramDividend.Classical.avram_bvb_obstruction_restricted_discounted_Stieltjes_cash_real_lower (μ : Measure ℝ) (A : Set ℝ)
    (hA : Ioc (0 : ℝ) (2 / 25 : ℝ) ⊆ A)
    (hMass : μ (Ioc (0 : ℝ) (2 / 25 : ℝ)) =
      ENNReal.ofReal (2 / 25 : ℝ))
    (hFin : (∫⁻ t in A,
      ENNReal.ofReal (Real.exp (-t)) ∂μ) ≠ ⊤) :
    (2 / 25 : ℝ) * Real.exp (-(1 / 10 : ℝ)) ≤
      (∫⁻ t in A,
        ENNReal.ofReal (Real.exp (-t)) ∂μ).toReal := by sorry
