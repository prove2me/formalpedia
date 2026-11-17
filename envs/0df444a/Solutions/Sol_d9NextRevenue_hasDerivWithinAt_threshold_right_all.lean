-- Prove2me | solution 1 for d9NextRevenue_hasDerivWithinAt_threshold_right_all
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T09:43:01.016754+00:00
-- url     : https://prove2.me/submissions/a9ecfc70-3767-4c3a-8470-be3b1b281991

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_d9NextRevenue
import Theorems.Thm_d9NextRevenue_hasDerivWithinAt_threshold_right
open NestedSeatAlloc.IntPolicy

theorem d9NextRevenue_hasDerivWithinAt_threshold_right_all
    (g : ℝ → ℝ) (p x fare s r : ℝ)
    (hG : HasDerivWithinAt g r (Set.Ici p) p) (hx : 0 ≤ x) :
    HasDerivWithinAt (fun u => d9NextRevenue g u x fare s)
      (if p < s ∧ s ≤ p + x then r - fare else 0)
      (Set.Ici p) p := by
  split_ifs with h
  · exact d9NextRevenue_hasDerivWithinAt_threshold_right g p x fare s r hG h.1 h.2
  · by_cases hsp : s ≤ p
    · apply (hasDerivWithinAt_const p (Set.Ici p) (g s)).congr
      · intro u hu
        have hu' : p ≤ u := hu
        simp only [d9NextRevenue]
        split_ifs with h1 h2
        · rfl
        · have : u = s := by linarith
          subst this
          simp
        · have : u = s := by linarith
          have hx0 : x = 0 := by linarith
          subst this
          subst hx0
          simp
      · simp only [d9NextRevenue]
        split_ifs with h1 h2
        · rfl
        · have : p = s := by linarith
          subst this
          simp
        · have : p = s := by linarith
          have hx0 : x = 0 := by linarith
          subst this
          subst hx0
          simp
    · push_neg at hsp
      have hs2 : p + x < s := by
        by_contra hc
        push_neg at hc
        exact h ⟨hsp, hc⟩
      apply (hasDerivWithinAt_const p (Set.Ici p) (x * fare + g (s - x))).congr_of_eventuallyEq
      · filter_upwards [mem_nhdsWithin_of_mem_nhds (isOpen_Iio.mem_nhds
          (show p < s - x by linarith))] with u hu
        have hu' : u < s - x := hu
        simp only [d9NextRevenue, if_neg (show ¬ s < u by linarith),
          if_neg (show ¬ s < u + x by linarith)]
      · simp only [d9NextRevenue, if_neg (show ¬ s < p by linarith),
          if_neg (show ¬ s < p + x by linarith)]

theorem solution
    (g : ℝ → ℝ) (p x fare s r : ℝ)
    (hG : HasDerivWithinAt g r (Set.Ici p) p) (hx : 0 ≤ x) :
    HasDerivWithinAt (fun u => d9NextRevenue g u x fare s)
      (if p < s ∧ s ≤ p + x then r - fare else 0)
      (Set.Ici p) p := by
  split_ifs with h
  · exact d9NextRevenue_hasDerivWithinAt_threshold_right g p x fare s r hG h.1 h.2
  · by_cases hsp : s ≤ p
    · apply (hasDerivWithinAt_const p (Set.Ici p) (g s)).congr
      · intro u hu
        have hu' : p ≤ u := hu
        simp only [d9NextRevenue]
        split_ifs with h1 h2
        · rfl
        · have : u = s := by linarith
          subst this
          simp
        · have : u = s := by linarith
          have hx0 : x = 0 := by linarith
          subst this
          subst hx0
          simp
      · simp only [d9NextRevenue]
        split_ifs with h1 h2
        · rfl
        · have : p = s := by linarith
          subst this
          simp
        · have : p = s := by linarith
          have hx0 : x = 0 := by linarith
          subst this
          subst hx0
          simp
    · push_neg at hsp
      have hs2 : p + x < s := by
        by_contra hc
        push_neg at hc
        exact h ⟨hsp, hc⟩
      apply (hasDerivWithinAt_const p (Set.Ici p) (x * fare + g (s - x))).congr_of_eventuallyEq
      · filter_upwards [mem_nhdsWithin_of_mem_nhds (isOpen_Iio.mem_nhds
          (show p < s - x by linarith))] with u hu
        have hu' : u < s - x := hu
        simp only [d9NextRevenue, if_neg (show ¬ s < u by linarith),
          if_neg (show ¬ s < u + x by linarith)]
      · simp only [d9NextRevenue, if_neg (show ¬ s < p by linarith),
          if_neg (show ¬ s < p + x by linarith)]


