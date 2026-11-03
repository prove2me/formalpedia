-- Prove2me | solution 1 for levy_foundations_finiteDimDistributionProjective
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T22:41:15.20922+00:00
-- url     : https://prove2.me/submissions/10e55968-bafb-4e9e-89f2-8fc3246581ac

import Mathlib.MeasureTheory.Constructions.Projective
import Definitions.Def_levy_foundations_finiteDimMap
import Definitions.Def_levy_foundations_finiteDimDistribution
import Theorems.Thm_levy_foundations_finiteDimDistributionRestrict
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal
theorem solution {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω}
    (hX : ∀ t, Measurable (X t)) :
    IsProjectiveMeasureFamily (α := fun (_ : ℝ≥0) => E)
      (LevyFoundations.finiteDimDistribution X μ) := by
  exact fun _ _ hJI => (levy_foundations_finiteDimDistributionRestrict hX hJI).symm
