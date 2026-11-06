-- Prove2me | solution 2 for levy_foundations_projectiveFamily_sigma_subadditive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T08:39:29.25137+00:00
-- url     : https://prove2.me/submissions/80e4b2e5-f0a1-49d1-830c-bcbea9ece66c

import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.Constructions.ClosedCompactCylinders
import Mathlib.Topology.MetricSpace.Polish
import Definitions.Def_levy_foundations_projectiveFamily
import Theorems.Thm_levy_foundations_projectiveFamily_content_tendsto_zero

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
  (projectiveFamilyContent pf.consistent).IsSigmaSubadditive := by
  letI : ∀ J : Finset ι, IsProbabilityMeasure (pf.measure J) := pf.prob
  refine isSigmaSubadditive_of_addContent_iUnion_eq_tsum
    isSetRing_measurableCylinders (fun f hf hf_Union hf' ↦ ?_)
  exact addContent_iUnion_eq_sum_of_tendsto_zero isSetRing_measurableCylinders
    (projectiveFamilyContent pf.consistent)
    (fun _ _ ↦ projectiveFamilyContent_ne_top pf.consistent)
    (fun {s} hs hs_anti hs_inter ↦
      levy_foundations_projectiveFamily_content_tendsto_zero pf hs hs_anti hs_inter)
    hf hf_Union hf'
