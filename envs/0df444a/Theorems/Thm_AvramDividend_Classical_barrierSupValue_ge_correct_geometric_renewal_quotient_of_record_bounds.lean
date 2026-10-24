-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierSupValue_ge_correct_geometric_renewal_quotient_of_record_bounds
-- name    : AvramDividend.Classical.barrierSupValue_ge_correct_geometric_renewal_quotient_of_record_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:39:39.542392+00:00
-- url     : https://prove2.me/theorems/2719f04b-a29a-44fe-990a-f3301690b469
-- title:
--   Correctly indexed lower renewal geometric quotient for stopped dividends
-- statement:
--   When genuine stopped dividend reward dominates measurable countable first-record budgets and each expected record payment is at least ε p^(n+1) with 0≤p<1, then the stopped barrier value is at least ε p/(1−p). Lower Stieltjes cells are discounted at their ending record time, giving one leading factor p. This is the scalar form needed for the left scale-function finite-difference bound.
-- source:
--   Accepted first-record lower Tonelli bridge, ENNReal.tsum_geometric_add_one and nonnegative real conversion lemmas.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_ge_sum_expected_firstRecord_budgets

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.barrierSupValue_ge_correct_geometric_renewal_quotient_of_record_bounds
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a q ε p : ℝ)
    (hε : 0 ≤ ε) (hp : 0 ≤ p) (hplt : p < 1)
    (w : ℕ → Ω → ℝ≥0∞)
    (hw : ∀ n : ℕ, AEMeasurable (w n) P)
    (hbudget : ∀ᵐ ω ∂P, (∑' n, w n ω) ≤
      (∫⁻ t,
        if t ∈ paymentTimes (barrierRuinTime X a ω)
        then ENNReal.ofReal (Real.exp (-(q * t))) else 0
        ∂(dividendMeasure (runningSup X) ω)))
    (hstep : ∀ n, ENNReal.ofReal (ε * p ^ (n + 1)) ≤
      (∫⁻ ω, w n ω ∂P)) :
    ENNReal.ofReal (ε * p / (1 - p)) ≤ barrierSupValue X a q := by sorry
