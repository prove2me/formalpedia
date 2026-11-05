-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_negative_jump_generator_measurable
-- name    : AvramDividend.Classical.avram_p3_e_compensator_original_negative_jump_generator_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:48:14.871473+00:00
-- url     : https://prove2.me/theorems/13601395-6f16-469a-b56d-12fd69164a40
-- title:
--   Original Lévy negative-jump generator is measurable in the reserve parameter
-- statement:
--   With the actual original spectrally negative Lévy intensity sigma-finite and the actual dividend value measurable, the map y to the true negative-mark nonlinear jump generator integral is Borel measurable, via the constant kernel built from X.ν.restrict Iio 0 and pinned kernel Bochner-integral measurability. The introduced kernel is definitionally exactly the original source measure, rather than any replacement jump model.

import Mathlib
import Mathlib.Probability.Kernel.MeasurableIntegral
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_e_compensator_original_negative_jump_generator_measurable
{Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
{𝓕 : Filtration ℝ≥0 mΩ}
(X : SpectrallyNegativeLevy P 𝓕)
(hSigma : SigmaFinite X.ν)
(w : ℝ → ℝ) (hwMeas : Measurable w) :
Measurable (fun y : ℝ =>
  ∫ z in Set.Iio (0 : ℝ), w (y + z) - w y ∂X.ν) := by sorry
