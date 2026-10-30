-- Prove2me | solution 1 for finite_extension_maximal_by_measure__p2m_a06e74bc_2d14_4a85_b8d6_42f2136549b3_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:40:00.816865+00:00
-- url     : https://prove2.me/submissions/e7de9160-e03c-4f45-a15f-d23cbe7382fc

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {α : Type} [Fintype α]
    (R : α → α → Prop)
    (measure : α → Nat)
    (P : α → Prop)
    (hrefl : ∀ a, R a a)
    (htrans : ∀ a b c, R a b → R b c → R a c)
    (hstrict : ∀ a b, R a b → a ≠ b → measure a < measure b)
    (x : α) (hx : P x) :
    ∃ y, R x y ∧ P y ∧ ∀ z, R y z → P z → z = y := by
  classical
  let S : Finset α := Finset.univ.filter (fun a => R x a ∧ P a)
  have hS : S.Nonempty := by
    refine ⟨x, ?_⟩
    simp [S, hrefl x, hx]
  obtain ⟨y, hyS, hyMax⟩ := Finset.exists_max_image S measure hS
  have hy : R x y ∧ P y := by
    simpa [S] using hyS
  refine ⟨y, hy.1, hy.2, ?_⟩
  intro z hyz hPz
  by_contra hzy
  have hzS : z ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨htrans x y z hy.1 hyz, hPz⟩
  have hlt : measure y < measure z := hstrict y z hyz (Ne.symm hzy)
  exact (not_lt_of_ge (hyMax z hzS)) hlt