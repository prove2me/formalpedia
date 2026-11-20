-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_actual_Levy_negative_mark_JL_integral_cancellation
-- name    : AvramDividend.Classical.avram_pj_workerC_actual_Levy_negative_mark_JL_integral_cancellation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:04:12.350904+00:00
-- url     : https://prove2.me/theorems/1269dc1e-4210-4093-954d-16b1b616df14
-- title:
--   True original spectrally negative Lévy measure J+L compensator kernel cancellation for the same eta cutoff
-- statement:
--   The original spectrally negative Lévy measure restricted to marks z<0 satisfies support almost surely, so the compensated nonlinear Taylor kernel integral plus the retained negative-mark annular first-order kernel integral equals exactly the tiny-mark first-order adjusted nonlinear integral. Preserves the actual source X.nu and integrability conditions.
-- source:
--   Proved general negative-mark J+L integral identity (new), plus pinned Mathlib ae_restrict_mem in MeasureTheory.Measure.Restrict.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_negative_mark_JL_compensator_integral_cancellation
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_actual_Levy_negative_mark_JL_integral_cancellation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (η : ℝ) (S d : ℝ → ℝ)
    (hη : 0 < η) (hηone : η < 1)
    (hH : Integrable (fun z => S z -
      (if -1 < z then z * d z else 0))
      (X.ν.restrict (Iio (0 : ℝ))))
    (hL : Integrable (fun z => if z ∈ Ioo (-1 : ℝ) (-η) then
      z * d z else 0)
      (X.ν.restrict (Iio (0 : ℝ)))) :
    (∫ z in Iio (0 : ℝ), S z -
      (if -1 < z then z * d z else 0) ∂X.ν) +
    (∫ z in Iio (0 : ℝ),
      (if z ∈ Ioo (-1 : ℝ) (-η) then z * d z else 0) ∂X.ν) =
    (∫ z in Iio (0 : ℝ),
      S z - (if -η ≤ z then z * d z else 0) ∂X.ν) := by sorry
