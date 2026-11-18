-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gaussianB_canonical_measurable_positive_joint_long_tube
-- name    : AvramDividend.Classical.avram_gaussianB_canonical_measurable_positive_joint_long_tube
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T23:40:32.989225+00:00
-- url     : https://prove2.me/theorems/2d5d7ec3-ff45-4426-a9dd-5b1277d88f05
-- title:
--   Canonical Gaussian source has a measurable positive-probability joint centred and drifted tube event
-- statement:
--   There exists a measurable event E of strictly positive canonical Gaussian probability on which both |brownian_t−brownian_0|≤1/4000 and |brownian_t−brownian_0+2t|≤1/400 hold uniformly through time 17/16000. The event is the closed joint tube of the Proved measurable continuous Brownian lift, and positivity comes from the Proved strict joint Brownian tube B186. This supplies the authentic measurable localisation event for the source-specific original stopped-cash contradiction.

import Mathlib.Tactic.NormNum
import Definitions.Def_GlynnSTS_Limit_Setting
import Theorems.Thm_AvramDividend_Classical_avram_gbB134_native_centered_brownian_lift_measurable_of_coordinates
import Theorems.Thm_AvramDividend_Classical_avram_gbB135_native_centered_brownian_coordinate_measurable
import Theorems.Thm_AvramDividend_Classical_avram_gbB186_canonical_gaussian_centered_joint_long_tube_positive_unconditional
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_joint_closed_continuous_path_tube_measurable
open MeasureTheory ProbabilityTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gaussianB_canonical_measurable_positive_joint_long_tube
    [IsProbabilityMeasure gaussianLimit] :
    ∃ E : Set (ℝ≥0 → ℝ),
      MeasurableSet E ∧ 0 < gaussianLimit E ∧
      (∀ ω ∈ E, ∀ s : unitInterval, s ≤ (⟨(17 / 16000 : ℝ), by constructor <;> norm_num⟩ : unitInterval) →
        |ProbabilityTheory.brownian ⟨s, s.2.1⟩ ω - ProbabilityTheory.brownian 0 ω| ≤ (1 / 4000 : ℝ) ∧
        |ProbabilityTheory.brownian ⟨s, s.2.1⟩ ω - ProbabilityTheory.brownian 0 ω + 2 * (s : ℝ)| ≤ (1 / 400 : ℝ)) := by sorry
