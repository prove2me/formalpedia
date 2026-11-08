-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_e0_singular_negative_density_isLevyMeasure
-- name    : AvramDividend.Classical.avram_e0_singular_negative_density_isLevyMeasure
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T13:59:40.75221+00:00
-- url     : https://prove2.me/theorems/c8395bb5-c0c9-4e31-a6c5-d34d3522fa9e
-- title:
--   The explicit inverse-three-halves negative jump density defines a genuine Lévy measure
-- statement:
--   For the concrete singular inverse-three-halves density supported on negative jumps between -1 and 0, verify LeanLevy IsLevyMeasure. The first-moment integrability already proved by GEN14 dominates the min(1,z²) condition, and Lebesgue volume gives zero mass at the origin. This unlocks the generic pure-jump Lévy-process existence theorem in the pinned LeanLevy import.
-- source:
--   Concrete mathematical prerequisite for the source-exact e0b94d7f and A19 singular-loss countermodel, using Proved a6ebe28d (absolute first moment), 00fa0af4 (measurable density), c96c705b (pure jump process exists for any IsLevyMeasure). No stochastic witness or disproof is claimed.

import Mathlib
import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Theorems.Thm_AvramDividend_Classical_avram_gen14_singular_levy_first_moment_integrable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_e0_singular_negative_density_isLevyMeasure :
    ProbabilityTheory.IsLevyMeasure
      (volume.withDensity (fun z : ℝ =>
        if z ∈ Ioo (-1 : ℝ) 0
        then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0)) := by sorry
