-- Prove2me | solution 1 for exists_maximal_supergraph_of_hereditary_property__p2m_4d37fe7f_2e72_452b_8439_d9da71f76f12_a2
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T17:18:39.582329+00:00
-- url     : https://prove2.me/submissions/c2bac156-6d42-4f77-91f6-08ef98e1360d

import Mathlib

set_option linter.unusedVariables false

theorem solution
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (K : SimpleGraph V)
    (hK : P K)
    (hhered : ∀ G H : SimpleGraph V, H.edgeSet ⊆ G.edgeSet → P G → P H) :
    ∃ N : SimpleGraph V,
      K.edgeSet ⊆ N.edgeSet ∧
      P N ∧
      ∀ M : SimpleGraph V,
        N.edgeSet ⊆ M.edgeSet →
        P M →
        M.edgeSet = N.edgeSet := by
  classical
  let p : SimpleGraph V → Prop := fun H => P H ∧ K.edgeSet ⊆ H.edgeSet
  have hpK : p K := ⟨hK, by simp⟩
  obtain ⟨N, _hKN, hmax⟩ :=
    (Finite.exists_le_maximal (α := SimpleGraph V) (p := p) (a := K) hpK)
  rcases hmax with ⟨hpN, hmax'⟩
  refine ⟨N, hpN.2, hpN.1, ?_⟩
  intro M hNM hPM
  have hle : N ≤ M := SimpleGraph.edgeSet_subset_edgeSet.mp hNM
  have hpM : p M := ⟨hPM, fun e he => hNM (hpN.2 he)⟩
  have hMN : M.edgeSet ⊆ N.edgeSet :=
    SimpleGraph.edgeSet_mono (hmax' hpM hle)
  exact le_antisymm hMN hNM
