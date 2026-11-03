-- Prove2me | solution 1 for finite_simpleGraph_has_maximal_extension__p2m_f3863ecb_d96f_4f01_8e13_caf8f4700d63_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-02T20:04:37.273189+00:00
-- url     : https://prove2.me/submissions/56030ba1-dda1-40aa-b489-55d6044a70e9

import Theorems.Thm_WilliamsonShmoys_exists_maximal_invariant_extension__p2m_ae139772_cde8_4644_bb54_63943db19887_a1

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop) (G : SimpleGraph V)
    (hG : P G)
    (hdown : ∀ ⦃A B : SimpleGraph V⦄, A ≤ B → P B → P A) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ P H ∧
      ∀ K : SimpleGraph V, H ≤ K → P K → K = H :=
  WilliamsonShmoys.exists_maximal_invariant_extension__p2m_ae139772_cde8_4644_bb54_63943db19887_a1 P G hG