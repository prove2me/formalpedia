-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_epsilon_large_jump_intensity_finite
-- name    : AvramDividend.Classical.avram_p4_c_generator_epsilon_large_jump_intensity_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:16:55.971278+00:00
-- url     : https://prove2.me/theorems/23f951a3-7c41-4e79-b5b4-7c8c2e9c7ca6
-- title:
--   Original Lévy jump intensity is finite on every negative mark band strictly separated from zero
-- statement:
--   For the genuine original negative Lévy measure and any epsilon>0, the mark set z<-epsilon has finite ν intensity. This follows from the source-specific Proved negative_jump_truncation_measure_finite on z≤-epsilon by measured monotonicity, with no independence or Poisson counting property assumed. It is exactly the finite-intensity prerequisite for a separated large-jump decomposition, while original stochastic rate/compensation remains P2's responsibility.
-- source:
--   negative_jump_truncation_measure_finite and source X.ν_integrable

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_c_generator_epsilon_large_jump_intensity_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ε : ℝ) (hε : 0 < ε) :
    X.ν (Iio (-ε)) < ⊤ := by sorry
