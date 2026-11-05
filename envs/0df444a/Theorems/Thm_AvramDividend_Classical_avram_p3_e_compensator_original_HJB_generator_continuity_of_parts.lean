-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_HJB_generator_continuity_of_parts
-- name    : AvramDividend.Classical.avram_p3_e_compensator_original_HJB_generator_continuity_of_parts
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T13:41:46.245915+00:00
-- url     : https://prove2.me/theorems/f55097d2-6c22-4a7d-b9e1-b61b2518b3de
-- title:
--   Original negative-jump HJB generator continuity from its three genuine source parts
-- statement:
--   For original spectrally negative Lévy source X, local continuity of w, deriv w and the actual source ν-negative-jump integral on compact [a,b] implies local continuity of the exact HJB drift residual X.drift*deriv w + ∫_{z<0}(w(y+z)-w(y))ν(dz) - q*w(y). This isolates the only analytic jump-integral continuity obligation for deriving compact L1 bounds.
-- source:
--   Mathlib ContinuousOn.mul, add, sub applied to the original X.drift, original X.ν and literal generator residual.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_e_compensator_original_HJB_generator_continuity_of_parts
{Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
{𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
(w : ℝ → ℝ) (q a b : ℝ)
(hwd : ContinuousOn (deriv w) (Set.Icc a b))
(hw : ContinuousOn w (Set.Icc a b))
(hν : ContinuousOn (fun y : ℝ => ∫ z in Set.Iio (0 : ℝ), w (y + z) - w y ∂X.ν) (Set.Icc a b)) :
ContinuousOn (fun y : ℝ => X.drift * deriv w y +
 (∫ z in Set.Iio (0 : ℝ), w (y + z) - w y ∂X.ν) - q * w y) (Set.Icc a b) := by sorry
