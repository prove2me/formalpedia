-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_11_original_ruin_clock_finite_expectation_of_uniform_nat_bound
-- name    : AvramDividend.Classical.avram_wave7_11_original_ruin_clock_finite_expectation_of_uniform_nat_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:36:09.098502+00:00
-- url     : https://prove2.me/theorems/632b274a-8069-44e0-a913-afe6484b6c6e
-- title:
--   Uniform finite real natural-clock dividend budgets imply finite original-process Stieltjes expectation
-- statement:
--   For the exact original Levy model and admissible dividend strategy, if each natural-clock truncated finite-horizon expected discounted Stieltjes reward is bounded by the ENNReal embedding of one finite real B, then the expected full-ruin reward up to the same finite real T is strictly below infinity. The original state space, ruin clock, payment sets and dividendMeasure are unchanged. The proved uniform-clock expectation inequality e43bdc5f supplies the finite global bound and ENNReal.ofReal_lt_top converts it to strict finiteness.
-- source:
--   Direct corollary of Proved W7-11 original ruin-clock uniform bound e43bdc5f, useful to W7-12 for original-process dividend value finiteness.

import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_original_ruin_clock_uniform_nat_budget_to_value

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_11_original_ruin_clock_finite_expectation_of_uniform_nat_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q T B : ℝ)
    (hBound : ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
          ENNReal.ofReal B) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) < ⊤ := by sorry
