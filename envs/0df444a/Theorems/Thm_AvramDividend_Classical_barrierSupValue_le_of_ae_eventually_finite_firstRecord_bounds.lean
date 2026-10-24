-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierSupValue_le_of_ae_eventually_finite_firstRecord_bounds
-- name    : AvramDividend.Classical.barrierSupValue_le_of_ae_eventually_finite_firstRecord_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T22:34:15.304788+00:00
-- url     : https://prove2.me/theorems/d270a66e-d5ff-4d01-b9c2-20ad7baaa45e
-- title:
--   Almost surely finite record-cell covers bound the stopped barrier value
-- statement:
--   Suppose each sample path admits a finite initial collection of measurable nonnegative first-record cell weights covering the genuine stopped dividend Stieltjes reward, with the finite cutoff allowed to depend on the sample path. Then its expected stopped reflected barrier value does not exceed the series of cell expectations. The argument embeds the finite upper cover into the supremum of partial sums and uses the established Tonelli bridge.
-- source:
--   Pinned Mathlib ENNReal.tsum_eq_iSup_nat and Prove2Me barrierSupValue_le_sum_expected_firstRecord_budgets.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_le_sum_expected_firstRecord_budgets

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal BigOperators Classical

theorem AvramDividend.Classical.barrierSupValue_le_of_ae_eventually_finite_firstRecord_bounds
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (a q : ℝ)
    (w : ℕ → Ω → ℝ≥0∞)
    (hw : ∀ n : ℕ, AEMeasurable (w n) P)
    (hfinite : ∀ᵐ ω ∂P, ∃ N : ℕ,
      (∫⁻ t,
        if t ∈ paymentTimes (barrierRuinTime X a ω)
        then ENNReal.ofReal (Real.exp (-(q * t))) else 0
        ∂(dividendMeasure (runningSup X) ω)) ≤
      (∑ n ∈ Finset.range N, w n ω)) :
    barrierSupValue X a q ≤ (∑' n, ∫⁻ ω, w n ω ∂P) := by sorry
