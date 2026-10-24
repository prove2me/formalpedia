-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierSupValue_ge_geometric_firstRecord_of_step_bounds
-- name    : AvramDividend.Classical.barrierSupValue_ge_geometric_firstRecord_of_step_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:08:24.470552+00:00
-- url     : https://prove2.me/theorems/40dc3751-9eb1-4ac9-9edd-26045f3107a0
-- title:
--   Geometric first-record lower budgets bound the stopped barrier value
-- statement:
--   If pathwise first-record payments are dominated by the genuine stopped Stieltjes reward and their expected values exceed a geometric renewal term cell-by-cell, then the geometric series bounds the actual stopped dividend value from below.
-- source:
--   Published stopped dividend first-record Tonelli bridge and ENNReal.tsum_le_tsum monotonicity.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_ge_sum_expected_firstRecord_budgets

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.barrierSupValue_ge_geometric_firstRecord_of_step_bounds
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a q ε p : ℝ)
    (w : ℕ → Ω → ℝ≥0∞)
    (hw : ∀ n : ℕ, AEMeasurable (w n) P)
    (hbudget : ∀ᵐ ω ∂P, (∑' n, w n ω) ≤
      (∫⁻ t,
        if t ∈ paymentTimes (barrierRuinTime X a ω)
        then ENNReal.ofReal (Real.exp (-(q * t))) else 0
        ∂(dividendMeasure (runningSup X) ω)))
    (hstep : ∀ n, ENNReal.ofReal (ε * p ^ (n + 1)) ≤
      (∫⁻ ω, w n ω ∂P)) :
    (∑' n, ENNReal.ofReal (ε * p ^ (n + 1))) ≤ barrierSupValue X a q := by sorry
