-- Prove2me | solution 1 for coordinateOpenBoxes_eq_openBoxes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:15:24.947317+00:00
-- url     : https://prove2.me/submissions/e98ec3f6-05b6-43df-9b99-5ec4cc9b662a

import Definitions.Def_ProbabilityTheory_chapter_02_def_2_8_F000
import Definitions.Def_ProbabilityTheory_chapter_02_thm_2_8_F000
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic

-- import Mathlib.Data.Real.Pointwise

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set MeasureTheory MeasurableSpace

open scoped Pointwise


theorem solution (d : ℕ) :
    Set.pi Set.univ '' Set.pi Set.univ (fun _ : Fin d => realOpenIntervals) =
      openBoxes d := by
  ext s
  constructor
  · rintro ⟨U, hU, rfl⟩
    have hU' : ∀ i : Fin d, U i ∈ realOpenIntervals := by
      intro i
      exact hU i (by simp)
    have hU'' : ∀ i : Fin d, ∃ a b : ℝ, a < b ∧ U i = Ioo a b := by
      intro i
      simpa [realOpenIntervals] using hU' i
    choose a b hab hEq using hU''
    refine ⟨a, b, hab, ?_⟩
    ext x
    simp [hEq]
  · rintro ⟨a, b, hab, rfl⟩
    refine ⟨fun i => Ioo (a i) (b i), ?_, rfl⟩
    intro i _hi
    exact ⟨a i, b i, hab i, rfl⟩