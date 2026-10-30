-- Prove2me | solution 1 for exists_maximal_simpleGraph_supergraph_of_finite__p2m_4cee4fb6_81c0_44bc_ba4b_b191f8c55242_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:29:00.248716+00:00
-- url     : https://prove2.me/submissions/cfd9b290-7da5-48c6-b28e-256e4be01b3e

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [DecidableEq V]
    (L : SimpleGraph V) (P : SimpleGraph V → Prop) (hL : P L) :
    ∃ M : SimpleGraph V, L ≤ M ∧ P M ∧
      ∀ N : SimpleGraph V, M ≤ N → P N → N ≤ M := by
  classical
  let Q : SimpleGraph V → Prop := fun G => P G ∧ L ≤ G
  have hQ : ∃ G : SimpleGraph V, Q G := ⟨L, hL, le_rfl⟩
  obtain ⟨M, dM, hM⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists Q).2 hQ
  letI : DecidableRel M.Adj := dM
  have hExt := hM
  rcases hM with ⟨hQM, _hMax⟩
  change P M ∧ L ≤ M at hQM
  refine ⟨M, hQM.2, hQM.1, ?_⟩
  intro N hMN hPN
  have hQN : Q N := ⟨hPN, le_trans hQM.2 hMN⟩
  have hEq : M = N := (SimpleGraph.IsExtremal.le_iff_eq hExt hQN).mp hMN
  exact le_of_eq hEq.symm