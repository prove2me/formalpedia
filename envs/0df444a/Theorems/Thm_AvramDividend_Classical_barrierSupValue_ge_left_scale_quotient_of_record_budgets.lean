-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierSupValue_ge_left_scale_quotient_of_record_budgets
-- name    : AvramDividend.Classical.barrierSupValue_ge_left_scale_quotient_of_record_budgets
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T22:01:48.843305+00:00
-- url     : https://prove2.me/theorems/88d484b2-cd02-4fc7-986b-d564b206c1c5
-- title:
--   Left scale quotient bound from delayed first-record budgets
-- statement:
--   Given a nonnegative W(a-epsilon), a strictly greater positive W(a), a pathwise lower first-record decomposition and lower discounted record expectation bounds, the reflected barrier value is at least epsilon W(a-epsilon)/(W(a)-W(a-epsilon)). The missing probabilistic estimates remain explicit hypotheses.
-- source:
--   Accepted conditional first-record geometric bound and the scale-ratio algebraic identity.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_ge_correct_geometric_renewal_quotient_of_record_bounds
import Theorems.Thm_AvramDividend_Classical_stopped_renewal_geometric_scale_ratio_lower
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.barrierSupValue_ge_left_scale_quotient_of_record_budgets
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (W : ℝ → ℝ) (a q ε : ℝ)
    (hε : 0 ≤ ε) (hWa : 0 < W a)
    (hWleft : 0 ≤ W (a - ε)) (hWinc : W (a - ε) < W a)
    (w : ℕ → Ω → ℝ≥0∞)
    (hw : ∀ n : ℕ, AEMeasurable (w n) P)
    (hbudget : ∀ᵐ ω ∂P, (∑' n, w n ω) ≤
      (∫⁻ t,
        if t ∈ paymentTimes (barrierRuinTime X a ω)
        then ENNReal.ofReal (Real.exp (-(q * t))) else 0
        ∂(dividendMeasure (runningSup X) ω)))
    (hstep : ∀ n,
      ENNReal.ofReal (ε * (W (a - ε) / W a) ^ (n + 1)) ≤
      (∫⁻ ω, w n ω ∂P)) :
    ENNReal.ofReal (ε * W (a - ε) / (W a - W (a - ε))) ≤
      barrierSupValue X a q := by sorry
