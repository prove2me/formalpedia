-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierSupValue_le_right_scale_quotient_of_record_budgets
-- name    : AvramDividend.Classical.barrierSupValue_le_right_scale_quotient_of_record_budgets
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T22:02:01.655549+00:00
-- url     : https://prove2.me/theorems/8198e109-b6ab-4de5-8770-e7e389a06893
-- title:
--   Right scale quotient bound from immediate first-record budgets
-- statement:
--   Given a nonnegative scale function value W(a), a strictly greater positive W(a+epsilon), a pathwise upper first-record decomposition and upper discounted record expectation bounds, the reflected barrier value is at most epsilon W(a+epsilon)/(W(a+epsilon)-W(a)). The missing probabilistic estimates remain explicit hypotheses.
-- source:
--   Accepted conditional first-record geometric bound and the scale-ratio algebraic identity.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_le_correct_geometric_renewal_quotient_of_record_bounds
import Theorems.Thm_AvramDividend_Classical_stopped_renewal_geometric_scale_ratio_upper
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.barrierSupValue_le_right_scale_quotient_of_record_budgets
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (W : ℝ → ℝ) (a q ε : ℝ)
    (hε : 0 ≤ ε) (hWright : 0 < W (a + ε))
    (hWa : 0 ≤ W a) (hWinc : W a < W (a + ε))
    (w : ℕ → Ω → ℝ≥0∞)
    (hw : ∀ n : ℕ, AEMeasurable (w n) P)
    (hbudget : ∀ᵐ ω ∂P,
      (∫⁻ t,
        if t ∈ paymentTimes (barrierRuinTime X a ω)
        then ENNReal.ofReal (Real.exp (-(q * t))) else 0
        ∂(dividendMeasure (runningSup X) ω)) ≤ (∑' n, w n ω))
    (hstep : ∀ n, (∫⁻ ω, w n ω ∂P) ≤
      ENNReal.ofReal (ε * (W a / W (a + ε)) ^ n)) :
    barrierSupValue X a q ≤
      ENNReal.ofReal (ε * W (a + ε) / (W (a + ε) - W a)) := by sorry
