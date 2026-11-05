-- Prove2me | solution 1 for levy_foundations_kolmogorovExtensionGivenSigmaSubadditive_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:30:41.724032+00:00
-- url     : https://prove2.me/submissions/7af891e8-a3cf-42cd-b989-4ca7250ff3a8

import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.Constructions.ClosedCompactCylinders
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.Topology.MetricSpace.Polish
import Definitions.Def_levy_foundations_projectiveFamily
import Definitions.Def_levy_foundations_kolmogorovExtensionGivenSigmaSubadditive
import Theorems.Thm_levy_foundations_kolmogorovExtensionGivenSigmaSubadditive_cylinder

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

/-! Equality of all cylinder marginals yields a projective limit. -/
theorem solution
    {ι : Type*} {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] [∀ i, TopologicalSpace (α i)]
    [∀ i, PolishSpace (α i)] [∀ i, BorelSpace (α i)]
    (pf : LevyFoundations.ProjectiveFamily ι α)
    (hσ : (projectiveFamilyContent pf.consistent).IsSigmaSubadditive) :
    IsProjectiveLimit (LevyFoundations.kolmogorovExtensionGivenSigmaSubadditive pf hσ)
      pf.measure := by
  intro I
  ext S hS
  rw [Measure.map_apply (Finset.measurable_restrict I) hS, ← cylinder]
  exact levy_foundations_kolmogorovExtensionGivenSigmaSubadditive_cylinder
    pf hσ I hS
