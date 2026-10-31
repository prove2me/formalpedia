-- Prove2me | solution 1 for finite_hereditary_maximal_extension__p2m_b4d9d994_9c3d_480d_8aaa_85ca7382f67c_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:08:06.687468+00:00
-- url     : https://prove2.me/submissions/2cc95bb4-ffb4-4892-bb12-05e56ee032ee

import Mathlib
set_option autoImplicit false

theorem solution
    {α : Type} [Fintype α] (r : α → α → Prop) (P : α → Prop)
    (score : α → Nat)
    (hrefl : ∀ a, r a a)
    (htrans : ∀ a b c, r a b → r b c → r a c)
    (hantisymm : ∀ a b, r a b → r b a → a = b)
    (hhered : ∀ a b, r b a → P a → P b)
    (hscore : ∀ a b, r a b → score a ≤ score b)
    (x : α) (hx : P x) :
    ∃ y, r x y ∧ P y ∧ score x ≤ score y ∧
      ∀ z, r y z → P z → z = y := by
  classical
  letI : PartialOrder α :=
    { le := r
      le_refl := hrefl
      le_trans := htrans
      le_antisymm := hantisymm }
  let S : Type := {a : α // r x a ∧ P a}
  let s : Finset S := Finset.univ
  let a0 : S := ⟨x, hrefl x, hx⟩
  have ha0 : a0 ∈ s := by simp [s]
  obtain ⟨y, hxy, hymax⟩ := s.exists_le_maximal ha0
  refine ⟨y.1, ?_, y.2.2, ?_, ?_⟩
  · change r x y.1 at hxy
    exact hxy
  · change r x y.1 at hxy
    exact hscore x y.1 hxy
  · intro z hyz hz
    let z0 : S := ⟨z, htrans x y.1 z (by
      change r x y.1 at hxy
      exact hxy) hyz, hz⟩
    have hz0 : z0 ∈ s := by simp [s]
    have hzy : z0 ≤ y := Maximal.le_of_ge hymax hz0 hyz
    change r z y.1 at hzy
    exact hantisymm z y.1 hzy hyz