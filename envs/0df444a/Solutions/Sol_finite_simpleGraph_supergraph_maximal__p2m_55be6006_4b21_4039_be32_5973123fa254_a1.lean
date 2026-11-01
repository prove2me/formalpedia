-- Prove2me | solution 1 for finite_simpleGraph_supergraph_maximal__p2m_55be6006_4b21_4039_be32_5973123fa254_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:19:24.469052+00:00
-- url     : https://prove2.me/submissions/e37817e9-7e3a-4e91-8d21-60314a20be6a

import Mathlib

theorem solution
    {V : Type} [Fintype V]
    (K : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hK : P K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ P L ∧
      ∀ M : SimpleGraph V, L ≤ M → P M → M ≤ L := by
  classical
  let S : Set (SimpleGraph V) := {L | K ≤ L ∧ P L}
  have hSfinite : S.Finite := Set.toFinite S
  have hSnonempty : S.Nonempty := ⟨K, by simp [S, hK]⟩
  obtain ⟨L, hLS, hLmax⟩ := hSfinite.exists_maximal hSnonempty
  refine ⟨L, hLS.1, hLS.2, ?_⟩
  intro M hLM hPM
  exact hLmax ⟨hLS.1.trans hLM, hPM⟩ hLM