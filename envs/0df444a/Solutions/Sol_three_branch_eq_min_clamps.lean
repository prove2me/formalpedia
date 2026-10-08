-- Prove2me | solution 1 for three_branch_eq_min_clamps
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T16:12:42.175636+00:00
-- url     : https://prove2.me/submissions/61576808-f525-426b-a22b-3efeafab51c6

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem solution
    (g h : ℝ → ℝ) (a c y s : ℝ) (ha : 0 ≤ a) (hy : 0 ≤ y)
    (hs : 0 ≤ s) (hg : ∀ t, g t = c * t + h t)
    (hleft : MonotoneOn h (Set.Icc 0 a))
    (hright : AntitoneOn h (Set.Ici a)) :
    (if s < a then g s else if s < a + y then (s - a) * c + g a
      else y * c + g (s - y)) =
      c * s + min (h (min s a)) (h (max (s - y) a)) := by
  by_cases hsa : s < a
  · have hsa' : s ≤ a := le_of_lt hsa
    have hsya : s - y ≤ a := by linarith
    have hle : h s ≤ h a :=
      hleft ⟨hs, hsa'⟩ ⟨ha, le_rfl⟩ hsa'
    simp [hsa, min_eq_left hsa', max_eq_right hsya, hg, min_eq_left hle]
  · by_cases hsb : s < a + y
    · have has : a ≤ s := le_of_not_gt hsa
      have hsya : s - y ≤ a := by linarith
      simp [hsa, hsb, min_eq_right has, max_eq_right hsya, hg]
      ring
    · have hbs : a + y ≤ s := le_of_not_gt hsb
      have has : a ≤ s := by linarith
      have hays : a ≤ s - y := by linarith
      have hle : h (s - y) ≤ h a :=
        hright (Set.mem_Ici.mpr le_rfl)
          (Set.mem_Ici.mpr hays) hays
      simp [hsa, hsb, min_eq_right has, max_eq_left hays,
        hg, min_eq_right hle]
      ring
