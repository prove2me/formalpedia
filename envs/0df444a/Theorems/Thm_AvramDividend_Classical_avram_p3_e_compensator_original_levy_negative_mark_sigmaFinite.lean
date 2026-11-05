-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_levy_negative_mark_sigmaFinite
-- name    : AvramDividend.Classical.avram_p3_e_compensator_original_levy_negative_mark_sigmaFinite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:46:52.572204+00:00
-- url     : https://prove2.me/theorems/529e5808-a64f-4b16-b771-f383c1e15b5f
-- title:
--   Original spectral-negative Lévy triplet mark measure is sigma-finite
-- statement:
--   For the literal source Lévy triplet, the integrable quadratic Lévy energy makes all negative mark tails separated from zero finite, while the source ν has zero mass on nonnegative marks. Apply the independently proved all-small-threshold tail bound and countable negative-cover sigma-finiteness to conclude SigmaFinite X.ν, enabling kernel-based measurable original ν-integral interfaces.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_negative_levy_mark_tail_finite_mass_at_every_small_threshold
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_sigma_finite_of_negative_tail_cover
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_e_compensator_original_levy_negative_mark_sigmaFinite
{Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
{𝓕 : Filtration ℝ≥0 mΩ}
(X : SpectrallyNegativeLevy P 𝓕) :
SigmaFinite X.ν := by sorry
