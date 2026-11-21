-- Prove2me | solution 1 for exists_veryWeakN_of_not_compatible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T15:08:16.689811+00:00
-- url     : https://prove2.me/submissions/4af19960-36a9-45d2-85ff-07b7bd470bbc

import Mathlib
import Definitions.Def_Basic
import Theorems.Thm_perp_iff
attribute [local simp] perp_iff
section
variable {O : Type*} [Orthoset O]
variable {P : Type*} [PartialOrder P]
private lemma veryWeakN_aux (x y : P) (hxy : x < y)
    (hfall : ∀ z : P, ¬ (incompSet x ∪ incompSet y ⊆ incompSet z)) :
    ∃ a d : P, IsVeryWeakN a x y d := by
  -- x⊥ ⊄ y⊥: otherwise z = y witnesses compatibility
  have hx_not_sub : ¬ (incompSet x ⊆ incompSet y) := fun h =>
    hfall y (Set.union_subset h (Set.Subset.refl _))
  -- y⊥ ⊄ x⊥: otherwise z = x witnesses compatibility
  have hy_not_sub : ¬ (incompSet y ⊆ incompSet x) := fun h =>
    hfall x (Set.union_subset (Set.Subset.refl _) h)
  -- pick a ∈ x⊥ \ y⊥ and d ∈ y⊥ \ x⊥
  obtain ⟨a, ha_x, ha_y⟩ := Set.not_subset.mp hx_not_sub
  obtain ⟨d, hd_y, hd_x⟩ := Set.not_subset.mp hy_not_sub
  -- unfold incompSet membership
  simp only [incompSet, Set.mem_setOf_eq] at ha_x ha_y hd_y hd_x
  -- ha_x : x ⊥ a,  ha_y : ¬ y ⊥ a  →  comparable, so y ≤ a ∨ a ≤ y
  -- hd_y : y ⊥ d,  hd_x : ¬ x ⊥ d  →  comparable, so x ≤ d ∨ d ≤ x
  simp only [perp_iff, not_and_or, not_not] at ha_y hd_x
  -- a < y: y ≤ a gives x ≤ a contradicting ha_x; a = y gives x ⊥ y contradicting hxy
  have hay : a < y := by
    rcases ha_y with hya | hay
    · exact absurd (hxy.le.trans hya) ha_x.1
    · rcases hay.lt_or_eq with h | h
      · exact h
      · exact absurd hxy.le (h ▸ ha_x).1
  -- x < d: d ≤ x gives d ≤ y contradicting hd_y; d = x gives y ⊥ x contradicting hxy
  have hxd : x < d := by
    rcases hd_x with hxd | hdx
    · rcases hxd.lt_or_eq with h | h
      · exact h
      · exact absurd hxy.le (h.symm ▸ hd_y).2
    · exact absurd (hdx.trans hxy.le) hd_y.2
  -- witnesses: IsVeryWeakN a x y d
  exact ⟨a, d, hay, hxy, hxd, ⟨ha_x.2, ha_x.1⟩, hd_y⟩
end

set_option autoImplicit true
variable {O : Type*} [Orthoset O]
variable {P : Type*} [PartialOrder P]
theorem _root_.solution (hP : ¬ IsCompatible P) :
    ∃ a b c d : P, IsVeryWeakN a b c d := by
  unfold IsCompatible at hP
  push Not at hP
  obtain ⟨x, y, hxy_comp, hfall⟩ := hP
  -- x ≠ y: if x = y then z = x is a valid witness, contradicting hfall
  have hne : x ≠ y := fun heq =>
    hfall x (heq ▸ (Set.union_self _).subset)
  -- ¬ (x ⊥ y) gives x ≤ y or y ≤ x; with x ≠ y this is x < y or y < x
  simp only [perp_iff, not_and_or, not_not] at hxy_comp
  rcases hxy_comp with hle | hle
  · -- x < y: apply the helper directly
    obtain ⟨a, d, hvw⟩ := veryWeakN_aux x y (hle.lt_of_ne hne) hfall
    exact ⟨a, x, y, d, hvw⟩
  · -- y < x: swap roles; union is commutative so hfall still applies
    obtain ⟨a, d, hvw⟩ := veryWeakN_aux y x (hle.lt_of_ne (Ne.symm hne))
      (fun z hz => hfall z (Set.union_comm _ _ ▸ hz))
    exact ⟨a, y, x, d, hvw⟩
