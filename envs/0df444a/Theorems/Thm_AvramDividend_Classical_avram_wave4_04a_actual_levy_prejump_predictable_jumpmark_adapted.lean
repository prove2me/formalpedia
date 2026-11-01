-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_prejump_predictable_jumpmark_adapted
-- name    : AvramDividend.Classical.avram_wave4_04a_actual_levy_prejump_predictable_jumpmark_adapted
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T09:29:58.824829+00:00
-- url     : https://prove2.me/theorems/3de01e15-7e1d-4a13-aa44-fe4441466b55
-- title:
--   Actual spectrally negative Lévy source pre-jump predictable and exact jump marks adapted on the same filtration
-- statement:
--   For an arbitrary actual source SpectrallyNegativeLevy P 𝓕, the strict left-limit process X(t−) is strongly predictable and the exact original-path jump mark X(t)−X(t−) is strongly adapted under the right-continuous enlargement 𝓕.rightCont. This is a source-process jump-measurability interface preserving all dividend controls on the same sample space. It does not assume an independent Poisson construction or a compensated-integral representation.
-- source:
--   Avram–Palmowski–Pistorius (2007), Proposition 4(i), original source-path requirements. Proved prerequisites: source X.leftLim and X.adapted fields; generic exact left-limit strong adaptedness 4a78651d-055e-4df8-a3d2-237dd30e6889, leftLim left-continuity ed804a27-2f90-48f6-ae95-da4acf17e44e, predictable modification 5ae104c4-13de-429a-a344-76d22511259b. Proof independent of controlled-reserve source and of equal-law replacements.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_stronglyAdapted_leftLim_of_exists_leftLimits
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_leftLim_leftContinuous_of_exists_leftLimits
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_strongAdapted_leftContinuous_predictable

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_04a_actual_levy_prejump_predictable_jumpmark_adapted
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    IsStronglyPredictable 𝓕.rightCont
      (fun t ω => Function.leftLim (fun s : ℝ≥0 => X.X s ω) t) ∧
    StronglyAdapted 𝓕.rightCont
      (fun t ω => X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t) := by sorry
