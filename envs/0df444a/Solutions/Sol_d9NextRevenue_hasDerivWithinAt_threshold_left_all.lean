-- Prove2me | solution 1 for d9NextRevenue_hasDerivWithinAt_threshold_left_all
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T09:43:00.01338+00:00
-- url     : https://prove2.me/submissions/1dfe9666-e95b-4d72-979f-03c88dc68580

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_d9NextRevenue
import Theorems.Thm_d9NextRevenue_hasDerivWithinAt_threshold_left
open NestedSeatAlloc.IntPolicy

theorem d9NextRevenue_hasDerivWithinAt_threshold_left_all
    (g : ℝ → ℝ) (p x fare s r : ℝ)
    (hG : HasDerivWithinAt g r (Set.Iic p) p) (hx : 0 ≤ x) :
    HasDerivWithinAt (fun u => d9NextRevenue g u x fare s)
      (if p ≤ s ∧ s < p + x then r - fare else 0)
      (Set.Iic p) p := by
  split_ifs with h
  · exact d9NextRevenue_hasDerivWithinAt_threshold_left g p x fare s r hG h.1 h.2
  · by_cases hsp : s < p
    · apply (hasDerivWithinAt_const p (Set.Iic p) (g s)).congr_of_eventuallyEq
      · filter_upwards [mem_nhdsWithin_of_mem_nhds (isOpen_Ioi.mem_nhds hsp)] with u hu
        have hu' : s < u := hu
        simp only [d9NextRevenue, if_pos hu']
      · simp only [d9NextRevenue, if_pos hsp]
    · push_neg at hsp
      have hs2 : p + x ≤ s := by
        by_contra hc
        push_neg at hc
        exact h ⟨hsp, hc⟩
      apply (hasDerivWithinAt_const p (Set.Iic p) (x * fare + g (s - x))).congr
      · intro u hu
        have hu' : u ≤ p := hu
        simp only [d9NextRevenue, if_neg (show ¬ s < u by linarith),
          if_neg (show ¬ s < u + x by linarith)]
      · simp only [d9NextRevenue, if_neg (show ¬ s < p by linarith),
          if_neg (show ¬ s < p + x by linarith)]

theorem solution
    (g : ℝ → ℝ) (p x fare s r : ℝ)
    (hG : HasDerivWithinAt g r (Set.Iic p) p) (hx : 0 ≤ x) :
    HasDerivWithinAt (fun u => d9NextRevenue g u x fare s)
      (if p ≤ s ∧ s < p + x then r - fare else 0)
      (Set.Iic p) p := by
  split_ifs with h
  · exact d9NextRevenue_hasDerivWithinAt_threshold_left g p x fare s r hG h.1 h.2
  · by_cases hsp : s < p
    · apply (hasDerivWithinAt_const p (Set.Iic p) (g s)).congr_of_eventuallyEq
      · filter_upwards [mem_nhdsWithin_of_mem_nhds (isOpen_Ioi.mem_nhds hsp)] with u hu
        have hu' : s < u := hu
        simp only [d9NextRevenue, if_pos hu']
      · simp only [d9NextRevenue, if_pos hsp]
    · push_neg at hsp
      have hs2 : p + x ≤ s := by
        by_contra hc
        push_neg at hc
        exact h ⟨hsp, hc⟩
      apply (hasDerivWithinAt_const p (Set.Iic p) (x * fare + g (s - x))).congr
      · intro u hu
        have hu' : u ≤ p := hu
        simp only [d9NextRevenue, if_neg (show ¬ s < u by linarith),
          if_neg (show ¬ s < u + x by linarith)]
      · simp only [d9NextRevenue, if_neg (show ¬ s < p by linarith),
          if_neg (show ¬ s < p + x by linarith)]


