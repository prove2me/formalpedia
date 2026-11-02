-- Prove2me | solution 1 for finite_set_has_maximal_simplegraph_extension__p2m_3dd2f00a_a125_4333_88d9_0f94f3546b41_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:54:40.556216+00:00
-- url     : https://prove2.me/submissions/30512e03-dc15-4c81-bb58-c4ded6664c18

import Mathlib

open SimpleGraph

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (S : Set (SimpleGraph V)) (hS : S.Finite) (hne : S.Nonempty) :
    ∃ K ∈ S, ∀ L ∈ S, K ≤ L → L ≤ K := by
  obtain ⟨K, hK⟩ := hS.exists_maximal hne
  refine ⟨K, hK.1, ?_⟩
  intro L hL hKL
  exact hK.2 hL hKL