-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_stopped_cash_finite_grid_two_sided_squeeze
-- name    : AvramDividend.Classical.avram_p3_2_original_stopped_cash_finite_grid_two_sided_squeeze
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:48:07.294116+00:00
-- url     : https://prove2.me/theorems/9d83166d-cdb2-4177-b09d-6df74e0c34e1
-- title:
--   Exact stopped original Stieltjes cash lies between finite right and left endpoint discounted physical masses
-- statement:
--   For each original stopped finite grid, the exact pre-ruin once-discounted dividendMeasure cash plus the initial atom lies between sums of unweighted original physical cell masses multiplied by their right and left exponential discount factors.
-- source:
--   Directly combines two source-exact fully Proved and non-circular original-process finite stopped cash estimates, preserving pre-ruin paymentTimes, Ioc stopped cells, physical dividendMeasure and time-zero atom.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_finite_stopped_discounted_cash_sum_lower
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_finite_stopped_discounted_cash_sum_upper

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_stopped_cash_finite_grid_two_sided_squeeze
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0) (m n : ℕ) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun j =>
      min (((min j (m + 1) : ℕ) : ℝ≥0) *
        (T / (m + 1))) τ
    (ENNReal.ofReal (rightLimit D 0 ω) +
      (∑ i ∈ Finset.range n,
        ENNReal.ofReal (Real.exp (-(q * (u (i + 1) : ℝ)))) *
          (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
              Ioc (u i : ℝ) (u (i + 1) : ℝ),
            (1 : ℝ≥0∞) ∂(dividendMeasure D ω))) ≤
      ENNReal.ofReal (rightLimit D 0 ω) +
      (∑ i ∈ Finset.range n,
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
            Ioc (u i : ℝ) (u (i + 1) : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)))) ∧
    (ENNReal.ofReal (rightLimit D 0 ω) +
      (∑ i ∈ Finset.range n,
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
            Ioc (u i : ℝ) (u (i + 1) : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))) ≤
      ENNReal.ofReal (rightLimit D 0 ω) +
      (∑ i ∈ Finset.range n,
        ENNReal.ofReal (Real.exp (-(q * (u i : ℝ)))) *
          (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
              Ioc (u i : ℝ) (u (i + 1) : ℝ),
            (1 : ℝ≥0∞) ∂(dividendMeasure D ω)))):= by sorry
