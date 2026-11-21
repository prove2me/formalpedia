-- Prove2me | solution 1 for not_compatible_if_weakN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T15:07:56.562431+00:00
-- url     : https://prove2.me/submissions/3239abb3-b8ea-4e11-873a-352ab51ff4cd

import Mathlib
import Definitions.Def_Basic
import Theorems.Thm_perp_iff
attribute [local simp] perp_iff

set_option autoImplicit true
variable {O : Type*} [Orthoset O]
variable {P : Type*} [PartialOrder P]
theorem _root_.solution (a b c d : P) (h : IsWeakN a b c d) :
    ¬ IsCompatible P := by
  obtain ⟨hac, hbc, hbd, hab, hcd⟩ := h
  intro hcomp
  -- b and c are comparable (b < c), so compatibility applies
  obtain ⟨z, hz⟩ := hcomp b c (fun h => h.1 hbc.lt.le)
  -- z ⊥ a (a ∈ incompSet b since b ⊥ a) and z ⊥ d (d ∈ incompSet c since c ⊥ d)
  have hza : z ⊥ a := hz (Set.mem_union_left  _ (show b ⊥ a from ⟨hab.2, hab.1⟩))
  have hzd : z ⊥ d := hz (Set.mem_union_right _ hcd)
  -- ¬ z ⊥ b: otherwise z ∈ incompSet b, hence z ∈ incompSet z, giving z ⊥ z — impossible
  have hzb : ¬ (z ⊥ b) := fun h =>
    (hz (Set.mem_union_left _ (show b ⊥ z from ⟨h.2, h.1⟩))).1 le_rfl
  -- ¬ z ⊥ c: same argument on the right
  have hzc : ¬ (z ⊥ c) := fun h =>
    (hz (Set.mem_union_right _ (show c ⊥ z from ⟨h.2, h.1⟩))).1 le_rfl
  -- b < z: from ¬ z ⊥ b we get z ≤ b or b ≤ z;
  --        z ≤ b leads to z ≤ d (via hbd) contradicting z ⊥ d;
  --        b = z leads to b ≤ d (via hbd) contradicting z ⊥ d
  have hbz : b < z := by
    simp only [perp_iff, not_and_or, not_not] at hzb
    rcases hzb with hzb | hbz
    · exact absurd (hzb.trans hbd.le) hzd.1
    · rcases hbz.lt_or_eq with h | h
      · exact h
      · exact absurd (h ▸ hbd.le) hzd.1
  -- z < c: from ¬ z ⊥ c we get z ≤ c or c ≤ z;
  --        c ≤ z leads to a ≤ z (via hac) contradicting z ⊥ a;
  --        z = c leads to a ≤ c (via hac) contradicting z ⊥ a
  have hzc' : z < c := by
    simp only [perp_iff, not_and_or, not_not] at hzc
    rcases hzc with hzc | hcz
    · rcases hzc.lt_or_eq with h | h
      · exact h
      · exact absurd hac.le (h ▸ hza).2
    · exact absurd (hac.le.trans hcz) hza.2
  -- b < z < c contradicts b ⋖ c
  exact hbc.2 hbz hzc'
