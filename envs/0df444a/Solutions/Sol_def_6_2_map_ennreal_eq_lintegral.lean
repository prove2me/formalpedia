-- Prove2me | solution 1 for def_6_2_map_ennreal_eq_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T23:36:14.628239+00:00
-- url     : https://prove2.me/submissions/f43a395a-4905-4552-ac7e-1607a043323a

import Theorems.Thm_simpleFunctionIntegralDefined_map_ennreal
import Theorems.Thm_simpleFunctionIntegralValue_map_ennreal_eq_lintegral
import Definitions.Def_ProbabilityTheory_chapter_06_def_6_2_F001
import Definitions.Def_ProbabilityTheory_chapter_06_def_6_2_F000
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped BigOperators
variable {Ω : Type*} [MeasurableSpace Ω]

theorem solution
    (μ : Measure Ω) (X : SimpleFunc Ω ENNReal) :
    def_6_2 μ (X.map fun x : ENNReal => (x : EReal)) =
      some ((X.lintegral μ : ENNReal) : EReal) := by
  classical
  unfold def_6_2
  simp [
    simpleFunctionIntegralDefined_map_ennreal μ X,
    simpleFunctionIntegralValue_map_ennreal_eq_lintegral μ X
  ]
