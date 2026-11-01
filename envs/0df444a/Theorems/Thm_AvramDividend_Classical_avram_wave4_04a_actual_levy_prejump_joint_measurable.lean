-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_prejump_joint_measurable
-- name    : AvramDividend.Classical.avram_wave4_04a_actual_levy_prejump_joint_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T09:40:00.233698+00:00
-- url     : https://prove2.me/theorems/ea6b2bd2-10bf-42b7-944e-c9fb5e703942
-- title:
--   Original Lévy strict pre-jump evaluation jointly Borel measurable on the actual time–sample space
-- statement:
--   For any original SpectrallyNegativeLevy process X and its genuine sample space Ω, the map (t,ω)↦X_{t−}(ω), with the exact Mathlib strict left-limit modification including at t=0, is jointly measurable for Borel time × original sample σ-algebra. Construct time approximants from below via c_n(t)=t−t·2^{−n−1}, recover positive-time left limits from X.leftLim, treat the time-zero section using original strong adaptedness, and pass measurable compositions to their pointwise limit. No equal-in-law replacement is used.
-- source:
--   Avram–Palmowski–Pistorius (2007) Proposition 4(i) genuine source jump functional. Uses accepted source right-continuous joint evaluation 8aafec11-d8a5-443c-9386-270a0d5c8a04 and generic strongly adapted leftLim 4a78651d-055e-4df8-a3d2-237dd30e6889. Semantic child of 9d68c5c2-c2c9-4cf9-a3d8-48c7929b7fc1 to obey the 80-line early-split guard.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_stronglyAdapted_leftLim_of_exists_leftLimits

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_04a_actual_levy_prejump_joint_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    Measurable (fun z : ℝ≥0 × Ω =>
      Function.leftLim (fun s : ℝ≥0 => X.X s z.2) z.1) := by sorry
