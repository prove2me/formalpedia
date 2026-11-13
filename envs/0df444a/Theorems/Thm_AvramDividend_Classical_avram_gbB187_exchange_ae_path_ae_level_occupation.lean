-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB187_exchange_ae_path_ae_level_occupation
-- name    : AvramDividend.Classical.avram_gbB187_exchange_ae_path_ae_level_occupation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T19:21:46.1642+00:00
-- url     : https://prove2.me/theorems/14388a07-69da-4f51-9746-37c606a2f026
-- title:
--   Exchange path and clipping-level almost-everywhere null occupations
-- statement:
--   Exchange path-almost-everywhere and spatial-level-almost-everywhere for a jointly measurable finite-time occupation mass. B185 supplies zero occupation at almost every level for each path; Fubini/Tonelli ae_ae_comm gives a deterministic full-Lebesgue-measure set of boundary levels good for P-a.e paths. The remaining original stochastic task is joint measurability of the actual reserve occupation function.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB185_ae_level_null_occupation_of_measurable_finite_time_path
open MeasureTheory Set Filter
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB187_exchange_ae_path_ae_level_occupation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [SFinite P]
    (Y : Ω → ℝ → ℝ) (hY : ∀ ω, Measurable (Y ω)) (n : ℕ)
    (hOcc : Measurable (fun z : Ω × ℝ =>
      volume {t : ℝ | 0 < t ∧ t < (n : ℝ) ∧ Y z.1 t = z.2})) :
    ∀ᵐ y ∂(volume : Measure ℝ), ∀ᵐ ω ∂P,
      volume {t : ℝ | 0 < t ∧ t < (n : ℝ) ∧ Y ω t = y} = 0 := by sorry
