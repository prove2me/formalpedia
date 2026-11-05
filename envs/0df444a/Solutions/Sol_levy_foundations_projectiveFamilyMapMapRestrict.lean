-- Prove2me | solution 1 for levy_foundations_projectiveFamilyMapMapRestrict
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T11:09:55.897554+00:00
-- url     : https://prove2.me/submissions/62da93e9-5fa4-422f-8805-8d80c491dadc

import Mathlib.MeasureTheory.Constructions.Projective
import Definitions.Def_levy_foundations_projectiveFamily

open MeasureTheory

theorem solution
    {ι : Type*} {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (pf : LevyFoundations.ProjectiveFamily ι α)
    {I J K : Finset ι} (hJI : J ⊆ I) (hKJ : K ⊆ J) :
    ((pf.measure I).map (Finset.restrict₂ hJI)).map
      (Finset.restrict₂ hKJ) =
      (pf.measure I).map (Finset.restrict₂ (hKJ.trans hJI)) := by
  rw [Measure.map_map (Finset.measurable_restrict₂ hKJ) (Finset.measurable_restrict₂ hJI)]
  rfl
