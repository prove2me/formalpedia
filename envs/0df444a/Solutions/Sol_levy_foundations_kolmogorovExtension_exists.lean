-- Prove2me | solution 1 for levy_foundations_kolmogorovExtension_exists
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T19:04:16.185509+00:00
-- url     : https://prove2.me/submissions/c34f9100-3034-43e5-9e6c-9296e0cd22a9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.Constructions.ClosedCompactCylinders
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.MetricSpace.Polish
import Definitions.Def_levy_foundations_projectiveFamily
import Theorems.Thm_levy_foundations_projectiveFamily_sigma_subadditive

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
  (pf : LevyFoundations.ProjectiveFamily ι α) :
  ∃ μ : Measure (∀ i, α i), IsProjectiveLimit μ pf.measure := by
  classical
  letI (J : Finset ι) : IsProbabilityMeasure (pf.measure J) := pf.prob J
  let μ : Measure (∀ i, α i) :=
    (projectiveFamilyContent pf.consistent).measure
      isSetSemiring_measurableCylinders
      generateFrom_measurableCylinders.ge
      (levy_foundations_projectiveFamily_sigma_subadditive pf)
  refine ⟨μ, ?_⟩
  intro I
  ext s hs
  rw [Measure.map_apply (Finset.measurable_restrict I) hs, ← cylinder]
  have key : μ (cylinder I s) =
      projectiveFamilyContent pf.consistent (cylinder I s) := by
    dsimp [μ]
    exact AddContent.measure_eq _ _ generateFrom_measurableCylinders.symm _
      (cylinder_mem_measurableCylinders _ _ hs)
  rw [key, projectiveFamilyContent_cylinder pf.consistent hs]
