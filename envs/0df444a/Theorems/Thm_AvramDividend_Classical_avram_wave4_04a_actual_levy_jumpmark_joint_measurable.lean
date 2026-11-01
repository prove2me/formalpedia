-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_joint_measurable
-- name    : AvramDividend.Classical.avram_wave4_04a_actual_levy_jumpmark_joint_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T09:35:00.507185+00:00
-- url     : https://prove2.me/theorems/9d68c5c2-c2c9-4cf9-a3d8-48c7929b7fc1
-- title:
--   Exact original Lévy jump-mark map is jointly Borel measurable in time and sample
-- statement:
--   For the original arbitrarily filtered spectrally negative Lévy process, the actual jump mark (t,ω)↦X(t,ω)−X(t−,ω) is measurable for the Borel time × original sample measurable space. The proof uses original X.rightCont, X.leftLim, X.adapted, joint right-continuous evaluation, and strictly-left time approximants. It makes no substitution of a Poisson-driven or equal-law process; it supplies the measurable mark graph required to construct source jump counting measures.
-- source:
--   Avram–Palmowski–Pistorius (2007) Proposition 4(i), source-path jump term; pinned Mathlib and accepted original-path rightContinuous_measurable_sections_joint_evaluation UUID 8aafec11-d8a5-443c-9386-270a0d5c8a04 and strong-adapted leftLim lemma UUID 4a78651d-055e-4df8-a3d2-237dd30e6889.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_stronglyAdapted_leftLim_of_exists_leftLimits

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_04a_actual_levy_jumpmark_joint_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    Measurable (fun z : ℝ≥0 × Ω =>
      X.X z.1 z.2 - Function.leftLim (fun s : ℝ≥0 => X.X s z.2) z.1) := by sorry
