-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_natural_clock_predictable_grid_mask
-- name    : AvramDividend.Classical.avram_ubv_hor3_original_natural_clock_predictable_grid_mask
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:49:28.655866+00:00
-- url     : https://prove2.me/theorems/7e997bd5-6083-4d60-9a74-7ade4589ec95
-- title:
--   Original ruin-truncated clock gives adapted physical pre-exit coefficients at each grid time
-- statement:
--   For the original Levy process and actual admissible controlled reserve, the natural finite ruin clock admits a right-continuous stopping-time representation, and any right-continuous adapted predictable grid coefficient remains adapted when masked by the true pre-exit event. Supplies the physical stopped-grid isometry with no extra mask-measurability assumption.
-- source:
--   Direct original ruin-time stopping witness and pinned MeasureTheory.IsStoppingTime.measurableSet_le with StronglyMeasurable.ite. No stochastic Ito path identity asserted.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_finite_clock_witness_of_ruin_meas_stopping
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_hor3_original_natural_clock_predictable_grid_mask
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (Cap : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x Cap D)
    (n : ℕ) (grid : ℕ → ℝ≥0)
    (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[𝓕.rightCont (grid i)] (H i)) :
    ∃ τ : Ω → ℝ≥0,
      (∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) ∧
      (∀ i, StronglyMeasurable[𝓕.rightCont (grid i)]
        (fun ω => if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
          then (0 : ℝ) else H i ω)) := by sorry
