-- Prove2me | solution 1 for exists_maximal_supergraph_of_finite__p2m_561cdf23_b328_4e27_9dce_aabc2761bd72_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T21:57:53.271201+00:00
-- url     : https://prove2.me/submissions/d7ea79ec-e932-408d-aa79-077b74004e43

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (G : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hP : P G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ P H ∧
      (∀ K : SimpleGraph V, H ≤ K → P K → K ≤ H) := by
  classical
  let Q : SimpleGraph V → Prop := fun X => G ≤ X ∧ P X
  have hQ : Q G := ⟨le_rfl, hP⟩
  obtain ⟨H, _, hH⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists Q).2 ⟨G, hQ⟩
  refine ⟨H, hH.1.1, hH.1.2, ?_⟩
  intro K hHK hPK
  have hQK : Q K := ⟨hH.1.1.trans hHK, hPK⟩
  have hEq : H = K :=
    (SimpleGraph.IsExtremal.le_iff_eq hH hQK).mp hHK
  exact le_of_eq hEq.symm
