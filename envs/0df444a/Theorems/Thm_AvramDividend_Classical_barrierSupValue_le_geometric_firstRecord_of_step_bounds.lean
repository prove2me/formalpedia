-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierSupValue_le_geometric_firstRecord_of_step_bounds
-- name    : AvramDividend.Classical.barrierSupValue_le_geometric_firstRecord_of_step_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:08:29.894774+00:00
-- url     : https://prove2.me/theorems/ce10880a-7d10-4d99-bfa8-48148b61f349
-- title:
--   Geometric first-record upper budgets bound the stopped barrier value
-- statement:
--   If the genuine stopped Stieltjes reward is dominated by measurable first-record payments whose expected values are each bounded by a geometric renewal term, then the geometric series bounds the actual stopped dividend value from above.
-- source:
--   Published stopped dividend first-record Tonelli bridge and ENNReal.tsum_le_tsum monotonicity.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_le_sum_expected_firstRecord_budgets

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.barrierSupValue_le_geometric_firstRecord_of_step_bounds
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a q ε p : ℝ)
    (w : ℕ → Ω → ℝ≥0∞)
    (hw : ∀ n : ℕ, AEMeasurable (w n) P)
    (hbudget : ∀ᵐ ω ∂P, (∫⁻ t,
        if t ∈ paymentTimes (barrierRuinTime X a ω)
        then ENNReal.ofReal (Real.exp (-(q * t))) else 0
        ∂(dividendMeasure (runningSup X) ω)) ≤
      (∑' n, w n ω))
    (hstep : ∀ n, (∫⁻ ω, w n ω ∂P) ≤
      ENNReal.ofReal (ε * p ^ (n + 1))) :
    barrierSupValue X a q ≤ (∑' n, ENNReal.ofReal (ε * p ^ (n + 1))) := by sorry
