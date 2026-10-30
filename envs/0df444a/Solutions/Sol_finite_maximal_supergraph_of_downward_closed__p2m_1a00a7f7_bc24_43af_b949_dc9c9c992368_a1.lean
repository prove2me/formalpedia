-- Prove2me | solution 1 for finite_maximal_supergraph_of_downward_closed__p2m_1a00a7f7_bc24_43af_b949_dc9c9c992368_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:30:43.080221+00:00
-- url     : https://prove2.me/submissions/24ad41dd-c117-471e-bce4-94af8f3b0ee7

import Mathlib
import Theorems.Thm_finite_partial_order_maximal_extension__p2m_c7432618_08fc_4a77_9546_40c80146e77b_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (H : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hP : P H)
    (hdown : ∀ {G G' : SimpleGraph V}, G ≤ G' → P G' → P G) :
    ∃ K : SimpleGraph V, H ≤ K ∧ P K ∧
      ∀ L : SimpleGraph V, K ≤ L → P L → L = K := by
  exact finite_partial_order_maximal_extension__p2m_c7432618_08fc_4a77_9546_40c80146e77b_a1
    P H hP