-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_negative_jump_integral_continuousOn_of_dominated
-- name    : AvramDividend.Classical.avram_p3_e_compensator_original_negative_jump_integral_continuousOn_of_dominated
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:28:31.539109+00:00
-- url     : https://prove2.me/theorems/98c1b3bf-9ea7-45d6-a618-8f3698cd3166
-- title:
--   Original negative-jump generator integral continuous on a compact interior band by domination
-- statement:
--   For the original Lévy intensity X.ν restricted to negative marks, local almost-everywhere strong measurability, a single integrable dominating envelope uniform over the compact reserve band, and almost-everywhere continuity in the reserve parameter imply continuity of the actual negative-jump generator integral on that band. No replacement jump model or compensator is assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_e_compensator_original_negative_jump_integral_continuousOn_of_dominated
{Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
{𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
(w : ℝ → ℝ) (a b : ℝ) (bound : ℝ → ℝ)
(hMeas : ∀ y ∈ Set.Icc a b, AEStronglyMeasurable
  (fun z : ℝ => w (y + z) - w y) (X.ν.restrict (Set.Iio (0 : ℝ))))
(hBound : ∀ y ∈ Set.Icc a b, ∀ᵐ z ∂(X.ν.restrict (Set.Iio (0 : ℝ))),
  ‖w (y + z) - w y‖ ≤ bound z)
(hBoundInt : Integrable bound (X.ν.restrict (Set.Iio (0 : ℝ))))
(hCont : ∀ᵐ z ∂(X.ν.restrict (Set.Iio (0 : ℝ))),
  ContinuousOn (fun y : ℝ => w (y + z) - w y) (Set.Icc a b)) :
ContinuousOn (fun y : ℝ =>
  ∫ z in Set.Iio (0 : ℝ), w (y + z) - w y ∂X.ν) (Set.Icc a b) := by sorry
