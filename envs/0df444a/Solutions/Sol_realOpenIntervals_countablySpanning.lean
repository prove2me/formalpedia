-- Prove2me | solution 1 for realOpenIntervals_countablySpanning
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:15:07.978453+00:00
-- url     : https://prove2.me/submissions/a72d1269-62af-4026-96ba-2089abdd8e82

import Definitions.Def_ProbabilityTheory_chapter_02_def_2_8_F000
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


theorem solution : IsCountablySpanning realOpenIntervals := by
  refine ⟨fun n => Ioo (-(((n + 1 : ℕ) : ℝ))) (((n + 1 : ℕ) : ℝ)), ?_, ?_⟩
  · intro n
    refine ⟨-(((n + 1 : ℕ) : ℝ)), (((n + 1 : ℕ) : ℝ)), ?_, rfl⟩
    have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_pos n
    linarith
  · ext x
    constructor
    · intro _; simp
    · intro _
      rcases exists_nat_gt |x| with ⟨n, hn⟩
      refine mem_iUnion.2 ⟨n, ?_⟩
      have hn' : |x| < (((n + 1 : ℕ) : ℝ)) :=
        lt_trans hn (by exact_mod_cast Nat.lt_succ_self n)
      constructor
      · linarith [neg_abs_le x]
      · linarith [le_abs_self x]