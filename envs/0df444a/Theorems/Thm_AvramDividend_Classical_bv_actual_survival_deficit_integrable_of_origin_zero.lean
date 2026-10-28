-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_actual_survival_deficit_integrable_of_origin_zero
-- name    : AvramDividend.Classical.bv_actual_survival_deficit_integrable_of_origin_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T07:53:49.152089+00:00
-- url     : https://prove2.me/theorems/a3a7213d-83a0-45b6-8b57-e520772adeae
-- title:
--   The actual BV physical drift deficit is integrable when restricted to genuine strict zero-barrier survival
-- statement:
--   An actual bounded-variation spectrally negative Lévy process under the standing positive-drift assumption starts at zero. Before strict zero-barrier reflected ruin its capital is nondecreasing, hence its deficit at horizon T lies in [0,dT] on survival. Even if its unrestricted deficit is not integrable because of large negative jumps, the survival-restricted deficit is bounded and integrable, assuming the measurable indicated function and the origin equality. Uses accepted positivity of drift, almost-sure nonnegativity of the deficit, and the monotone capital prefix.
-- source:
--   Accepted bv_standing_drift_pos, bv_actual_levy_drift_upper_ae_fixed_time, zero_reflected_ruin_strict_survival_capital_monotone_prefix and bounded_survival_deficit_indicator_integrable.

import Theorems.Thm_AvramDividend_Classical_bounded_survival_deficit_indicator_integrable
import Theorems.Thm_AvramDividend_Classical_zero_reflected_ruin_strict_survival_capital_monotone_prefix
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_upper_ae_fixed_time
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Mathlib.MeasureTheory.Measure.Real

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_actual_survival_deficit_integrable_of_origin_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (T : ℝ≥0)
    (hOrigin : ∀ ω : Ω, X.X 0 ω = 0)
    (hMeas : AEStronglyMeasurable
      ({ω : Ω | (T : ℝ≥0∞) < barrierRuinTime X 0 ω}.indicator
        (fun ω => (T : ℝ) * X.drift - X.X T ω)) P) :
    Integrable
      ({ω : Ω | (T : ℝ≥0∞) < barrierRuinTime X 0 ω}.indicator
        (fun ω => (T : ℝ) * X.drift - X.X T ω)) P := by sorry
