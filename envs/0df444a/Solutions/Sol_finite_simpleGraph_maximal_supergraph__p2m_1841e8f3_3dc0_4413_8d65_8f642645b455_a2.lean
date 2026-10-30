-- Prove2me | solution 1 for finite_simpleGraph_maximal_supergraph__p2m_1841e8f3_3dc0_4413_8d65_8f642645b455_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:17:46.425029+00:00
-- url     : https://prove2.me/submissions/0998bab5-1628-4c8d-a4c7-9f0df9150eb7

import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (P : SimpleGraph V → Prop) (hP : P G) :
    ∃ K : SimpleGraph V, G ≤ K ∧ P K ∧
      ∀ L : SimpleGraph V, K ≤ L → P L → L ≤ K := by
  classical
  let Q : SimpleGraph V → Prop := fun H => G ≤ H ∧ P H
  obtain ⟨K, hKdec, hK⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists Q).2
      ⟨G, le_rfl, hP⟩
  letI := hKdec
  refine ⟨K, hK.1.1, hK.1.2, ?_⟩
  intro L hKL hPL
  have hQL : Q L := ⟨hK.1.1.trans hKL, hPL⟩
  have hEq : K = L :=
    (SimpleGraph.IsExtremal.le_iff_eq hK hQL).mp hKL
  exact le_of_eq hEq.symm