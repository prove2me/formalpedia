-- Prove2me | solution 1 for thm_2_4_increment_pairwise_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:21:35.786304+00:00
-- url     : https://prove2.me/submissions/a90b8c48-23c1-4957-841c-8f0f89ca9d10

import Definitions.Def_ProbabilityTheory_chapter_02_thm_2_4_F000
import Theorems.Thm_thm_2_4_increment_subset
import Definitions.Def_ProbabilityTheory_chapter_02_def_2_6_F000
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped BigOperators

theorem solution {Ω : Type*} {A : ℕ → Set Ω}
    (hA : SetSeqIncreasing A) :
    Pairwise (fun i j => Disjoint (thm_2_4_increment A i) (thm_2_4_increment A j)) := by
  change Monotone A at hA
  have hlt_disjoint :
      ∀ {i j : ℕ}, i < j → Disjoint (thm_2_4_increment A i) (thm_2_4_increment A j) := by
    intro i j hlt
    cases j with
    | zero =>
        omega
    | succ k =>
        have hi_le_k : i ≤ k := Nat.lt_succ_iff.mp hlt
        rw [disjoint_left]
        intro x hxi hxj
        have hxAi : x ∈ A i := thm_2_4_increment_subset A i hxi
        have hxAk : x ∈ A k := hA hi_le_k hxAi
        exact hxj.2 hxAk
  intro i j hij
  by_cases hlt : i < j
  · exact hlt_disjoint hlt
  · have hji : j < i := Nat.lt_of_le_of_ne (Nat.le_of_not_gt hlt) (Ne.symm hij)
    exact (hlt_disjoint hji).symm
