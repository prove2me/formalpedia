-- Prove2me | solution 1 for thm_2_7_iUnion_closedApprox_eq_Ioo
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:53:14.82851+00:00
-- url     : https://prove2.me/submissions/2af6a692-cbb1-46d8-9795-272d95b95eee

import Definitions.Def_ProbabilityTheory_chapter_02_thm_2_7_F000
import Definitions.Def_ProbabilityTheory_chapter_02_def_2_8_F000
import Definitions.Def_ProbabilityTheory_chapter_02_def_2_8_F001
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set MeasureTheory

theorem solution {a b : ℝ} (_hab : a < b) :
    (⋃ n : ℕ, thm_2_7_closedApprox a b n) = Set.Ioo a b := by
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨n, hn⟩
    dsimp [thm_2_7_closedApprox] at hn
    split_ifs at hn with hstrict
    · have hδpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
      exact ⟨by linarith [hn.1], by linarith [hn.2]⟩
    · simp at hn

  · intro hx
    have hleft_pos : 0 < x - a := by linarith [hx.1]
    have hright_pos : 0 < b - x := by linarith [hx.2]
    have hmin_pos : 0 < min (x - a) (b - x) := lt_min hleft_pos hright_pos
    rcases exists_nat_one_div_lt hmin_pos with ⟨n, hn⟩
    refine Set.mem_iUnion.mpr ⟨n, ?_⟩
    have hn_left : 1 / ((n : ℝ) + 1) < x - a :=
      lt_of_lt_of_le hn (min_le_left _ _)
    have hn_right : 1 / ((n : ℝ) + 1) < b - x :=
      lt_of_lt_of_le hn (min_le_right _ _)
    have hstrict :
        a + 1 / ((n : ℝ) + 1) < b - 1 / ((n : ℝ) + 1) := by
      linarith
    dsimp [thm_2_7_closedApprox]
    simpa [hstrict] using
      (show
          a + 1 / ((n : ℝ) + 1) < b - 1 / ((n : ℝ) + 1) ∧
            a + 1 / ((n : ℝ) + 1) ≤ x ∧
              x ≤ b - 1 / ((n : ℝ) + 1) from
        ⟨hstrict, by linarith, by linarith⟩)
