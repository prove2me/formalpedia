-- Prove2me | solution 1 for levy_foundations_charExponent_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:17:52.558949+00:00
-- url     : https://prove2.me/submissions/d0400413-5ff5-4587-8a13-6a579b280307

import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Definitions.Def_levy_foundations_isLevyProcess
import Definitions.Def_levy_foundations_charExponent
import Definitions.Def_levy_foundations_levyGoodDomain
import Definitions.Def_levy_foundations_levyLocalCharExponent
import Definitions.Def_levy_foundations_levyExpFormula

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
open scoped NNReal

/-! At the zero frequency, all probability characteristic functions equal one. -/
theorem solution
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableAdd₂ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : LevyFoundations.IsLevyProcess X μ)
    (hX : ∀ t, Measurable (X t)) :
    LevyFoundations.charExponent h (0 : E) = 0 := by
  simp only [LevyFoundations.charExponent]
  apply Filter.Tendsto.limUnder_eq
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  have : charFun (μ.map (X t)) (0 : E) = 1 := by
    haveI : IsProbabilityMeasure (μ.map (X t)) :=
      Measure.isProbabilityMeasure_map (hX t).aemeasurable
    simp [charFun_zero]
  rw [this, Complex.log_one, zero_div]
