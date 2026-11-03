-- Prove2me | solution 1 for levy_foundations_prodIteDisjoint
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:05:02.719321+00:00
-- url     : https://prove2.me/submissions/c8bf1538-a880-4ac1-b108-a61205b91e8d

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Notation.Indicator

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Finset Set
open Classical in

theorem solution
    {E ι : Type*} [Fintype ι]
    (A : ι → Set E) (hdisj : Pairwise (Function.onFun Disjoint A))
    (z : ι → ℂ) (x : E) :
    (∏ i, (if x ∈ A i then z i else 1)) =
      1 + ∑ i, (A i).indicator (fun _ => z i - 1) x := by
  classical
  by_cases hx : ∃ i, x ∈ A i
  · obtain ⟨i₀, hi₀⟩ := hx
    have huniq : ∀ i, i ≠ i₀ → x ∉ A i := by
      intro i hi hmem
      exact Set.disjoint_left.mp (hdisj hi) hmem hi₀
    rw [Finset.prod_eq_single i₀
        (fun i _ hi => if_neg (huniq i hi)) (by simp),
      if_pos hi₀,
      Finset.sum_eq_single i₀
        (fun i _ hi => Set.indicator_of_notMem (huniq i hi) _)
        (by simp),
      Set.indicator_of_mem hi₀]
    ring
  · push Not at hx
    rw [Finset.prod_eq_one (fun i _ => if_neg (hx i)),
      Finset.sum_eq_zero
        (fun i _ => Set.indicator_of_notMem (hx i) _)]
    ring
