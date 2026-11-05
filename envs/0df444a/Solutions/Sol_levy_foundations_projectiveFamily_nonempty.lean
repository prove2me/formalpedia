-- Prove2me | solution 1 for levy_foundations_projectiveFamily_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T11:09:54.609992+00:00
-- url     : https://prove2.me/submissions/d8ea9996-fc11-45b4-912f-87570d3f62f5

import Mathlib.MeasureTheory.Constructions.Projective
import Definitions.Def_levy_foundations_projectiveFamily

open MeasureTheory

theorem solution
    {ι : Type*} {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (pf : LevyFoundations.ProjectiveFamily ι α) (i : ι) :
    Nonempty (α i) := by
  haveI := pf.prob {i}
  obtain ⟨f⟩ : Nonempty (∀ j : ({i} : Finset ι), α j) := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := (pf.prob {i}).measure_univ
    rw [Set.univ_eq_empty_iff.mpr h, measure_empty] at this
    exact zero_ne_one this
  exact ⟨f ⟨i, Finset.mem_singleton_self i⟩⟩
