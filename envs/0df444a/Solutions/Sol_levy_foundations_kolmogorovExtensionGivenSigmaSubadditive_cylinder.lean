-- Prove2me | solution 1 for levy_foundations_kolmogorovExtensionGivenSigmaSubadditive_cylinder
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:25:33.665695+00:00
-- url     : https://prove2.me/submissions/1bb64f0a-d153-4cad-aeae-1918f3b42375

import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.Constructions.ClosedCompactCylinders
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.Topology.MetricSpace.Polish
import Definitions.Def_levy_foundations_projectiveFamily
import Definitions.Def_levy_foundations_kolmogorovExtensionGivenSigmaSubadditive

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

/-! Recover the cylinder mass of a Kolmogorov extension from the add-content measure. -/
theorem solution
    {ι : Type*} {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] [∀ i, TopologicalSpace (α i)]
    [∀ i, PolishSpace (α i)] [∀ i, BorelSpace (α i)]
    (pf : LevyFoundations.ProjectiveFamily ι α)
    (hσ : (projectiveFamilyContent pf.consistent).IsSigmaSubadditive)
    (I : Finset ι) {S : Set (∀ i : I, α i)} (hS : MeasurableSet S) :
    LevyFoundations.kolmogorovExtensionGivenSigmaSubadditive pf hσ (cylinder I S) =
      pf.measure I S := by
  have hkey : LevyFoundations.kolmogorovExtensionGivenSigmaSubadditive pf hσ (cylinder I S) =
      projectiveFamilyContent pf.consistent (cylinder I S) := by
    unfold LevyFoundations.kolmogorovExtensionGivenSigmaSubadditive
    exact AddContent.measure_eq _ _ generateFrom_measurableCylinders.symm _
      (cylinder_mem_measurableCylinders _ _ hS)
  rw [hkey, projectiveFamilyContent_cylinder pf.consistent hS]
