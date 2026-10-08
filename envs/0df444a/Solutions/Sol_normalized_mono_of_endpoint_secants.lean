-- Prove2me | solution 1 for normalized_mono_of_endpoint_secants
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T16:23:02.832468+00:00
-- url     : https://prove2.me/submissions/293934d0-dcb0-429e-87fb-47f6e60355a5

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem solution
    (g : ℝ → ℝ) (a c : ℝ) (ha : 0 ≤ a)
    (hconc : ConcaveOn ℝ (Set.Ici 0) g)
    (hleft : ∀ x, x ∈ Set.Icc 0 a → x < a → c ≤ slope g x a)
    (hright : ∀ y, a < y → slope g a y ≤ c) :
    MonotoneOn (fun x => g x - c * x) (Set.Icc 0 a) ∧
      AntitoneOn (fun x => g x - c * x) (Set.Ici a) := by
  constructor
  · intro x hx y hy hxy
    rcases lt_or_eq_of_le hxy with hxy | rfl
    · have hslope : c ≤ slope g x y := by
        by_cases hya : y = a
        · simpa [hya] using hleft x hx (by simpa [hya] using hxy)
        · have hya' : y < a := lt_of_le_of_ne hy.2 hya
          have hsec : slope g y a ≤ slope g x y := by
            simpa [slope_def_field] using
              (hconc.slope_anti_adjacent hx.1 ha hxy hya')
          exact le_trans (hleft y hy hya') hsec
      rw [slope_def_field] at hslope
      have hpos : 0 < y - x := sub_pos.mpr hxy
      have hmul : c * (y - x) ≤ g y - g x :=
        (le_div_iff₀ hpos).mp hslope
      nlinarith
    · simp
  · intro x hx y hy hxy
    rcases lt_or_eq_of_le hxy with hxy | rfl
    · have hslope : slope g x y ≤ c := by
        by_cases hxa : x = a
        · subst x
          exact hright y hxy
        · have hax : a < x := lt_of_le_of_ne (Set.mem_Ici.mp hx) (Ne.symm hxa)
          have hsec : slope g x y ≤ slope g a x := by
            simpa [slope_def_field] using
              (hconc.slope_anti_adjacent ha (le_trans ha (Set.mem_Ici.mp hy))
                hax hxy)
          exact le_trans hsec (hright x hax)
      rw [slope_def_field] at hslope
      have hpos : 0 < y - x := sub_pos.mpr hxy
      have hmul : g y - g x ≤ c * (y - x) :=
        (div_le_iff₀ hpos).mp hslope
      nlinarith
    · simp
