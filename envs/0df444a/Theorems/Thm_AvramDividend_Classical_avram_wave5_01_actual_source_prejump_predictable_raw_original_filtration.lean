-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_prejump_predictable_raw_original_filtration
-- name    : AvramDividend.Classical.avram_wave5_01_actual_source_prejump_predictable_raw_original_filtration
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T09:03:12.275082+00:00
-- url     : https://prove2.me/theorems/91d7344e-42cf-4ad7-9932-43cd53ab6975
-- title:
--   Actual original Lévy prejump process is predictable in the raw source filtration
-- statement:
--   For every original SpectrallyNegativeLevy P 𝓕, the genuine pathwise left-limit process X_{t-}(ω) is strongly predictable for the raw original filtration 𝓕 itself. The accepted raw-𝓕 strongly adapted prejump theorem and actual source left-limit left-continuity feed the Proved general adapted left-continuous predictability theorem. No enlargement, completion, BV, Poisson process or extra laws are assumed.
-- source:
--   Raw source prejump/jumpmark strong adaptedness 73fbc493; generic leftLim left-continuity and strongly adapted left-continuous predictable source theorems.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_original_raw_filtration_prejump_jumpmark_strongly_adapted
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_leftLim_leftContinuous_of_exists_leftLimits
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_strongAdapted_leftContinuous_predictable

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_01_actual_source_prejump_predictable_raw_original_filtration
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    IsStronglyPredictable 𝓕
      (fun t ω => Function.leftLim (fun s : ℝ≥0 => X.X s ω) t) := by sorry
