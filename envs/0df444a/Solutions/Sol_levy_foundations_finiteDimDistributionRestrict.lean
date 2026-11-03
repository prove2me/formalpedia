-- Prove2me | solution 1 for levy_foundations_finiteDimDistributionRestrict
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T22:39:21.264995+00:00
-- url     : https://prove2.me/submissions/637913ca-296b-4dcb-84f0-fb8a61814534

import Mathlib.MeasureTheory.Constructions.Projective
import Definitions.Def_levy_foundations_finiteDimMap
import Definitions.Def_levy_foundations_finiteDimDistribution
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal
theorem solution {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω}
    (hX : ∀ t, Measurable (X t))
    {I J : Finset ℝ≥0} (hJI : J ⊆ I) :
    (LevyFoundations.finiteDimDistribution X μ I).map
      (Finset.restrict₂ (π := fun _ => E) hJI) =
      LevyFoundations.finiteDimDistribution X μ J := by
  have hmap : Measurable (LevyFoundations.finiteDimMap X I) :=
    measurable_pi_lambda _ (fun i => hX i)
  simp only [LevyFoundations.finiteDimDistribution]
  rw [Measure.map_map]
  · rfl
  · exact Finset.measurable_restrict₂ hJI
  · exact hmap
