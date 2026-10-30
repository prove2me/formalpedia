-- Prove2me | solution 1 for finite_rel_maximal_extension__p2m_038327fe_4daf_4028_a7aa_65aa49782279_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T21:46:39.052745+00:00
-- url     : https://prove2.me/submissions/307400db-6a8f-47fe-99aa-7600473bd287

import Mathlib

set_option autoImplicit false

theorem solution {α : Type} [Finite α] (r : α → α → Prop)
    (hrefl : ∀ a, r a a)
    (htrans : ∀ a b c, r a b → r b c → r a c)
    (hantisymm : ∀ a b, r a b → r b a → a = b)
    (Q : α → Prop) (x : α) (hx : Q x) :
    ∃ y, Q y ∧ r x y ∧ ∀ z, Q z → r y z → r z y := by
  letI : PartialOrder α := {
    le := r
    lt := fun a b => r a b ∧ ¬ r b a
    le_refl := hrefl
    le_trans := htrans
    le_antisymm := hantisymm
    lt_iff_le_not_ge := fun _ _ => Iff.rfl
  }
  have hfin : {a : α | Q a}.Finite :=
    Set.finite_univ.subset (Set.subset_univ _)
  obtain ⟨y, hxy, hymax⟩ :=
    hfin.exists_le_maximal (s := {a : α | Q a}) hx
  rcases hymax with ⟨hy, hymax⟩
  refine ⟨y, hy, hxy, ?_⟩
  intro z hz hyz
  exact hymax hz hyz