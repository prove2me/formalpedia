-- Prove2me | solution 1 for levy_foundations_levyLocalCharExponent_continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:19:00.764208+00:00
-- url     : https://prove2.me/submissions/b9aede87-4732-4201-9c35-eae522915c6b

import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Definitions.Def_levy_foundations_isLevyProcess
import Definitions.Def_levy_foundations_localLogGoodDomain
import Definitions.Def_levy_foundations_localLogExponent
import Definitions.Def_levy_foundations_levyGoodDomain
import Definitions.Def_levy_foundations_levyLocalCharExponent
import Theorems.Thm_levy_foundations_localLog_continuousOn_exponent

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
open scoped NNReal

/-! Continuity of the marginal characteristic function gives local-log continuity. -/
theorem solution
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableAdd₂ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : LevyFoundations.IsLevyProcess X μ)
    (hX : ∀ t, Measurable (X t)) :
    ContinuousOn (LevyFoundations.levyLocalCharExponent h hX)
      (LevyFoundations.levyGoodDomain h hX) := by
  haveI : IsFiniteMeasure (μ.map (X 1)) := Measure.isFiniteMeasure_map μ (X 1)
  exact levy_foundations_localLog_continuousOn_exponent
    (φ := fun ξ => charFun (μ.map (X 1)) ξ)
    (MeasureTheory.continuous_charFun)
