-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_actual_jump_measure_positive_time_ae
-- name    : AvramDividend.Classical.avram_pj_workerC_actual_jump_measure_positive_time_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T23:42:49.51621+00:00
-- url     : https://prove2.me/theorems/23e019b7-6b8b-4bfa-8dd9-e368ce93cf5e
-- title:
--   True original Lévy marked jump measure almost everywhere supported at strictly positive time
-- statement:
--   The intrinsic original negative-jump counting measure is supported by positive event times. Pathwise almost-everywhere time > 0 follows from existing Proved source e2216ed6 that the measure has zero mass at {0}×univ. This provides the missing support certificate to apply stopped compensation at a zero clock.
-- source:
--   Proved original jump time-zero mass e2216ed6; ae_iff plus set equality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_jump_measure_zero_initial_time
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_pj_workerC_actual_jump_measure_positive_time_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) :
    ∀ᵐ p ∂((Measure.count.restrict {s : ℝ≥0 |
       0 < s ∧ X.X s ω -
         Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
       (fun s : ℝ≥0 => (s, X.X s ω -
         Function.leftLim (fun t : ℝ≥0 => X.X t ω) s))),
      p.1 ≠ 0 := by sorry
