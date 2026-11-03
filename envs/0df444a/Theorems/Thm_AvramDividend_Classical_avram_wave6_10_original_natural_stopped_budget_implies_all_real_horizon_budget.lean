-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_10_original_natural_stopped_budget_implies_all_real_horizon_budget
-- name    : AvramDividend.Classical.avram_wave6_10_original_natural_stopped_budget_implies_all_real_horizon_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T08:45:32.570767+00:00
-- url     : https://prove2.me/theorems/9dcdd14a-09ba-4d42-b4db-2fb744143da8
-- title:
--   Every original real dividend horizon follows from natural stopped-horizon budgets with terminal atoms retained
-- statement:
--   For the actual SpectrallyNegativeLevy source X, its original dividend strategy D and Stieltjes payment measure, any uniform upper bound A for all deterministic natural ruin-stopped expected discounted dividend rewards implies the same bound for every nonnegative real-time closed horizon T. An integer strictly beyond T preserves a possible dividend payment atom at T, while the initial zero-time atom remains included. This is the exact converse local-to-global budget bridge to the already Proved min-clock subset lemma, and requires no additional stochastic-model assumptions.
-- source:
--   Canonical Proved paymentTimes_min_ofReal_eq_inter_Iio_of_pos 3634eef8-1dc4-4ba5-9478-4dbce286da9e; Archimedean exists_nat_gt; two exact ENNReal lintegral monotonicities under original dividendMeasure and P. A direct source-faithful alternative route for UBV finite-horizon bridge cc518136 when nat stopped budgets are available.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_ofReal_eq_inter_Iio_of_pos

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave6_10_original_natural_stopped_budget_implies_all_real_horizon_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (A : ℝ≥0∞)
    (hBound : ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in
        paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) ≤ A) :
    ∀ T : ℝ, 0 ≤ T →
      (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) ≤ A := by sorry
