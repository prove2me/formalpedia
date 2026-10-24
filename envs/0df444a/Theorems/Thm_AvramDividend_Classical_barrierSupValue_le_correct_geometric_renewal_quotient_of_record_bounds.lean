-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierSupValue_le_correct_geometric_renewal_quotient_of_record_bounds
-- name    : AvramDividend.Classical.barrierSupValue_le_correct_geometric_renewal_quotient_of_record_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:39:48.507928+00:00
-- url     : https://prove2.me/theorems/60735763-9c05-48b9-a449-f0c03c8fcd6e
-- title:
--   Correctly indexed upper renewal geometric quotient for stopped dividends
-- statement:
--   When the actual stopped dividend reward is pathwise dominated by measurable countable first-record budgets whose expected n-th payment is bounded by ε p^n for 0≤p<1, the stopped value is at most ε/(1−p). Crucially, the upper Riemann-Stieltjes cell is discounted at its starting record time, so the geometric series starts at n=0 and has no leading p factor. This is exactly the scalar shape required for the right scale finite-difference bound.
-- source:
--   Published first-record upper Tonelli bridge, ENNReal.tsum_geometric and Mathlib conversion of nonnegative real operations.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_le_sum_expected_firstRecord_budgets

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.barrierSupValue_le_correct_geometric_renewal_quotient_of_record_bounds
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a q ε p : ℝ)
    (hε : 0 ≤ ε) (hp : 0 ≤ p) (hplt : p < 1)
    (w : ℕ → Ω → ℝ≥0∞)
    (hw : ∀ n : ℕ, AEMeasurable (w n) P)
    (hbudget : ∀ᵐ ω ∂P,
      (∫⁻ t,
        if t ∈ paymentTimes (barrierRuinTime X a ω)
        then ENNReal.ofReal (Real.exp (-(q * t))) else 0
        ∂(dividendMeasure (runningSup X) ω))
      ≤ (∑' n, w n ω))
    (hstep : ∀ n, (∫⁻ ω, w n ω ∂P) ≤
      ENNReal.ofReal (ε * p ^ n)) :
    barrierSupValue X a q ≤ ENNReal.ofReal (ε / (1 - p)) := by sorry
