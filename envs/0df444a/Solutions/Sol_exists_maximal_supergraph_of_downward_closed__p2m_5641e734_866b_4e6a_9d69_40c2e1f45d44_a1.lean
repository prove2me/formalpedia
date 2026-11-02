-- Prove2me | solution 1 for exists_maximal_supergraph_of_downward_closed__p2m_5641e734_866b_4e6a_9d69_40c2e1f45d44_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:07:43.004043+00:00
-- url     : https://prove2.me/submissions/80ed6eb3-ef3d-4128-b64e-f74ae5f5ce50

import Mathlib

theorem solution
    {V : Type} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V → Prop)
    (hdown : ∀ {A B : SimpleGraph V}, A ≤ B → P B → P A)
    (G : SimpleGraph V) (hG : P G) :
    ∃ K : SimpleGraph V, G ≤ K ∧ P K ∧
      ∀ H : SimpleGraph V, K ≤ H → P H → H ≤ K := by
  classical
  let Q : SimpleGraph V → Prop := fun H => G ≤ H ∧ P H
  obtain ⟨K, hGK, hmax⟩ :=
    Finite.exists_le_maximal (p := Q) (a := G) ⟨le_rfl, hG⟩
  refine ⟨K, hGK, hmax.1.2, ?_⟩
  intro H hKH hPH
  have hQH : Q H := ⟨hGK.trans hKH, hPH⟩
  by_contra hnot
  exact hmax.not_prop_of_gt (lt_iff_le_not_ge.mpr ⟨hKH, hnot⟩) hQH