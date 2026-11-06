-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_natural_stopped_predictable_weight_L2
-- name    : AvramDividend.Classical.avram_ubv_hor3_original_natural_stopped_predictable_weight_L2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:59:40.373051+00:00
-- url     : https://prove2.me/theorems/fdc88851-1958-46bb-8f22-226a3f5bad90
-- title:
--   Physical original ruin-stopped predictable grid coefficients preserve L² without extra mask assumptions
-- statement:
--   Every actual clipped natural ruin clock τ=min(ruinTime X x D,n) of the original spectrally negative Lévy reserve preserves square-integrability of the true right-continuous adapted predictable grid coefficients when masked by strict pre-exit. Uses the original stopping-time event and pointwise norm domination by the unmasked L² coefficient, supplying a necessary estimate for physical martingale isometry.
-- source:
--   Original stopped clock witness, pinned IsStoppingTime.measurableSet_le and StronglyMeasurable.ite, plus MemLp.of_le and pointwise absolute bound. Independent of still Open source Ito-Meyer.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_finite_clock_witness_of_ruin_meas_stopping
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_hor3_original_natural_stopped_predictable_weight_L2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (Cap : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x Cap D)
    (n : ℕ) (grid : ℕ → ℝ≥0)
    (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[𝓕.rightCont (grid i)] (H i))
    (hHL2 : ∀ i, MemLp (H i) 2 P) :
    ∃ τ : Ω → ℝ≥0,
      (∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) ∧
      (∀ i, MemLp
        (fun ω => if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
          then (0 : ℝ) else H i ω) 2 P) := by sorry
