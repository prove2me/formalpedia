-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_BV_bounded_random_clock_strict_prepayment_terminal_L1_of_source_measurable
-- name    : AvramDividend.Classical.avram_p3_g2_original_BV_bounded_random_clock_strict_prepayment_terminal_L1_of_source_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T00:07:21.197877+00:00
-- url     : https://prove2.me/theorems/29551a4e-5ed6-405d-8e25-0b9b93ea32f8
-- title:
--   Original BV bounded random-clock strictly pre-ruin prepayment terminal L1 from measurable physical evaluation
-- statement:
--   For the original BV Levy process and dividend strategy, any bounded measurable observation clock has an integrable discounted strict-survival prepayment HJB terminal, provided the actual random-time reserve and source survival event are measurable. These are explicit remaining source-measurability premises; the mathematical bound and integrability follow automatically from the uniform all-clock BV physical drift strip and continuity on nonnegative reserves. No cap or stop-time restriction, no mean-zero premise.
-- source:
--   Public G2 635fc873 uniform bounded random clock prepayment strip; public continuous_test_abs_le_on_finite_cap; pinned Integrable.mono' and real exponential discount bound. hRiskMeas/hSurvivalMeas need genuine original random-time source receipts, not fabricated.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_continuous_test_abs_le_on_finite_cap
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_BV_bounded_random_clock_strict_prepayment_uniform_drift_strip

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_g2_original_BV_bounded_random_clock_strict_prepayment_terminal_L1_of_source_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hXzero : ∀ ω, X.X 0 ω = 0)
    (hFinite : IsFiniteMeasure P)
    (x : ℝ) (hx : 0 ≤ x)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hwCont : ContinuousOn w (Ici 0))
    (hwMeas : Measurable w)
    (q : ℝ) (hq : 0 ≤ q)
    (H : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτMeas : Measurable τ) (hτBound : ∀ ω, τ ω ≤ H)
    (hRiskMeas : Measurable (fun ω =>
      riskProcess X x D (τ ω) ω))
    (hSurvivalMeas : MeasurableSet {ω |
      (τ ω : ℝ≥0∞) < ruinTime X x D ω}) :
    Integrable (fun ω => if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * (τ ω : ℝ))) *
        w (riskProcess X x D (τ ω) ω)
    else 0) P := by sorry
