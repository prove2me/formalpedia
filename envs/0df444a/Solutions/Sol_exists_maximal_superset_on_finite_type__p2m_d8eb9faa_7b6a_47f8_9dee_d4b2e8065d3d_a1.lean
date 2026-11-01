-- Prove2me | solution 1 for exists_maximal_superset_on_finite_type__p2m_d8eb9faa_7b6a_47f8_9dee_d4b2e8065d3d_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:36:42.371187+00:00
-- url     : https://prove2.me/submissions/ae863496-551e-4c44-b48f-e38125c6549c

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_exists_maximal_under_relation_on_finite_type__p2m_d0cc2cac_35cc_4a64_9dcf_6596e31e9633_a1

set_option autoImplicit false

theorem solution
    {α β : Type} [Fintype α]
    (edge : α → Set β)
    (hedge : Function.Injective edge)
    (P : α → Prop)
    (A : α)
    (hA : P A) :
    ∃ B : α,
      edge A ⊆ edge B ∧
      P B ∧
      ∀ C : α, edge B ⊆ edge C → P C → edge C = edge B := by
  classical
  let R : α → α → Prop := fun x y => edge x ⊆ edge y
  have hRrefl : ∀ x, R x x := by
    intro x
    exact Set.Subset.rfl
  have hRtrans : ∀ x y z, R x y → R y z → R x z := by
    intro x y z hxy hyz
    exact Set.Subset.trans hxy hyz
  have hRantisymm : ∀ x y, R x y → R y x → x = y := by
    intro x y hxy hyx
    apply hedge
    exact Set.Subset.antisymm hxy hyx
  let S : α → Prop := fun x => P x ∧ edge A ⊆ edge x
  have hS : ∃ x, S x := by
    exact ⟨A, hA, Set.Subset.rfl⟩
  obtain ⟨B, hSB, hBmax⟩ :=
    exists_maximal_under_relation_on_finite_type__p2m_d0cc2cac_35cc_4a64_9dcf_6596e31e9633_a1
      R hRrefl hRtrans hRantisymm S hS
  refine ⟨B, hSB.2, hSB.1, ?_⟩
  intro C hBC hPC
  have hSC : S C := ⟨hPC, Set.Subset.trans hSB.2 hBC⟩
  have hCB : R C B := hBmax C hSC hBC
  exact Set.Subset.antisymm hCB hBC