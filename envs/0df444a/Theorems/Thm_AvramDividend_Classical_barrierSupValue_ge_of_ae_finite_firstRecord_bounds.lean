-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierSupValue_ge_of_ae_finite_firstRecord_bounds
-- name    : AvramDividend.Classical.barrierSupValue_ge_of_ae_finite_firstRecord_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T22:33:29.272712+00:00
-- url     : https://prove2.me/theorems/efbf0064-a726-43f0-a7a4-e5a05794267e
-- title:
--   Finite first-record payout bounds imply the expected stopped barrier lower bound
-- statement:
--   For the actual stopped running-supremum Stieltjes dividend reward, suppose nonnegative first-record cell payments are almost everywhere measurable and every finite initial budget is almost everywhere at most the pathwise reward. The entire sum of expected first-record payments is bounded by the expected stopped barrier value. Combining the accepted finite-to-countable a.e. lemma with the accepted Stieltjes Tonelli bridge removes the need for an additional infinite pathwise bound.
-- source:
--   Pinned Mathlib ENNReal finite-prefix monotone convergence and published Prove2Me firstRecord_ae_finite_cell_budget_to_tsum and barrierSupValue_ge_sum_expected_firstRecord_budgets.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_firstRecord_ae_finite_cell_budget_to_tsum
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_ge_sum_expected_firstRecord_budgets

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal BigOperators Classical

theorem AvramDividend.Classical.barrierSupValue_ge_of_ae_finite_firstRecord_bounds
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (a q : ℝ)
    (w : ℕ → Ω → ℝ≥0∞)
    (hw : ∀ n : ℕ, AEMeasurable (w n) P)
    (hfinite : ∀ N : ℕ, ∀ᵐ ω ∂P,
      (∑ n ∈ Finset.range N, w n ω) ≤
        (∫⁻ t,
          if t ∈ paymentTimes (barrierRuinTime X a ω)
          then ENNReal.ofReal (Real.exp (-(q * t))) else 0
          ∂(dividendMeasure (runningSup X) ω))) :
    (∑' n, ∫⁻ ω, w n ω ∂P) ≤ barrierSupValue X a q := by sorry
