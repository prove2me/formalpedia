-- Prove2me | solution 1 for levy_foundations_kolmogorovExtension_unique
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T13:17:37.638121+00:00
-- url     : https://prove2.me/submissions/8bbefa89-ac0c-4d5e-8377-ecebbca0cd52

import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.MetricSpace.Polish
import Definitions.Def_levy_foundations_projectiveFamily

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

theorem solution
  {ι : Type*} {α : ι → Type*}
  [∀ i, MeasurableSpace (α i)]
  [∀ i, TopologicalSpace (α i)]
  [∀ i, PolishSpace (α i)]
  [∀ i, BorelSpace (α i)]
  (pf : LevyFoundations.ProjectiveFamily ι α)
  (μ ν : Measure (∀ i, α i))
  (hμ : IsProjectiveLimit μ pf.measure)
  (hν : IsProjectiveLimit ν pf.measure) :
  μ = ν := by
  letI (I : Finset ι) : IsProbabilityMeasure (pf.measure I) := pf.prob I
  exact hμ.unique hν
