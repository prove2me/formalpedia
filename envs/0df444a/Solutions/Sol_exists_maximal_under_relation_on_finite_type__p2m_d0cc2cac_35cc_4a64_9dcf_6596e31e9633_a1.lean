-- Prove2me | solution 1 for exists_maximal_under_relation_on_finite_type__p2m_d0cc2cac_35cc_4a64_9dcf_6596e31e9633_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:42:49.947302+00:00
-- url     : https://prove2.me/submissions/b9aa4789-dad1-478c-9a2a-2dce0451a2cc

import Mathlib

set_option autoImplicit false

theorem solution
    {α : Type} [Fintype α]
    (R : α → α → Prop)
    (hRrefl : ∀ x, R x x)
    (hRtrans : ∀ x y z, R x y → R y z → R x z)
    (hRantisymm : ∀ x y, R x y → R y x → x = y)
    (S : α → Prop)
    (hS : ∃ x, S x) :
    ∃ b, S b ∧ ∀ c, S c → R b c → R c b := by
  classical
  letI : PartialOrder α :=
    { le := R
      le_refl := hRrefl
      le_trans := hRtrans
      le_antisymm := hRantisymm }
  let s : Finset α := Finset.univ.filter S
  have hs : s.Nonempty := by
    obtain ⟨x, hx⟩ := hS
    exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩⟩
  obtain ⟨b, hb⟩ := s.exists_maximal hs
  refine ⟨b, (Finset.mem_filter.mp hb.1).2, ?_⟩
  intro c hc hbc
  exact hb.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc⟩) hbc