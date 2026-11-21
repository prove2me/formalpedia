-- Prove2me | solution 1 for not_compatible_if_X
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T15:09:14.597139+00:00
-- url     : https://prove2.me/submissions/5474d156-0fb2-4315-ba87-80f00edcbedd

import Mathlib
import Definitions.Def_Basic
import Theorems.Thm_perp_iff
import Theorems.Thm_hasX_iff_hasCoveringX
import Theorems.Thm_not_compatible_if_weakN
attribute [local simp] perp_iff

set_option autoImplicit true
variable {O : Type*} [Orthoset O]
variable {P : Type*} [PartialOrder P]
theorem _root_.solution [Finite P] (a b c d m : P) (h : IsX a b c d m) :
    ¬ IsCompatible P := by
  -- Reduce to a covering X via hasX_iff_hasCoveringX
  obtain ⟨a, b, c, d, m, h1, h2, h3, h4, h5, h6⟩ :=
    hasX_iff_hasCoveringX.mp ⟨a, b, c, d, m, h⟩
  -- a < m ⋖ c, so a < c, hence a and c are comparable
  intro hcomp
  obtain ⟨z, hz⟩ := hcomp a c (fun h => h.1 (h1.trans h2.lt).le)
  -- z ⊥ b (b ∈ incompSet a via a ⊥ b = h5) and z ⊥ d (d ∈ incompSet c via c ⊥ d = h6)
  have hzb : z ⊥ b := hz (Set.mem_union_left  _ h5)
  have hzd : z ⊥ d := hz (Set.mem_union_right _ h6)
  -- ¬ z ⊥ a and ¬ z ⊥ c (same self-incomparability argument as in not_compatible_if_weakN)
  have hza : ¬ (z ⊥ a) := fun h =>
    (hz (Set.mem_union_left  _ (show a ⊥ z from ⟨h.2, h.1⟩))).1 le_rfl
  have hzc : ¬ (z ⊥ c) := fun h =>
    (hz (Set.mem_union_right _ (show c ⊥ z from ⟨h.2, h.1⟩))).1 le_rfl
  -- z < c: c ≤ z gives b ≤ z (via b < m < c ≤ z) contradicting z ⊥ b;
  --        z = c gives b ≤ c (via b < m < c) but (c ⊥ b = z ⊥ b) says ¬ b ≤ c
  have hzc' : z < c := by
    simp only [perp_iff, not_and_or, not_not] at hzc
    rcases hzc with hzc | hcz
    · rcases hzc.lt_or_eq with h | h
      · exact h
      · exact absurd (h3.trans h2.lt).le (h ▸ hzb).2
    · exact absurd ((h3.trans h2.lt).le.trans hcz) hzb.2
  -- a < z: z ≤ a gives z ≤ d (via a < m < d) contradicting z ⊥ d;
  --        z = a gives a ≤ d (via a < m < d) but (a ⊥ d = z ⊥ d) says ¬ a ≤ d
  have haz : a < z := by
    simp only [perp_iff, not_and_or, not_not] at hza
    rcases hza with hza | haz
    · exact absurd (hza.trans (h1.trans h4).le) hzd.1
    · rcases haz.lt_or_eq with h | h
      · exact h
      · exact absurd (h1.trans h4).le (h.symm ▸ hzd).1
  -- z ⊥ m: z < m gives z ≤ d (via m < d) contradicting z ⊥ d;
  --        m ≤ z gives b ≤ z (via b < m) contradicting z ⊥ b
  have hzm : z ⊥ m :=
    ⟨fun hzm => absurd (hzm.trans h4.le) hzd.1,
     fun hmz => absurd (h3.le.trans hmz) hzb.2⟩
  -- Now N^?(z, m, c, d): z < c, m ⋖ c, m < d, z ⊥ m, c ⊥ d
  exact not_compatible_if_weakN z m c d ⟨hzc', h2, h4, hzm, h6⟩ hcomp
