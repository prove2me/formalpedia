-- Prove2me | solution 1 for finite_maximal_drawable_edge_count_extension__p2m_4ae5c893_7e52_474c_915d_3ed4ab7c0e94_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:40:09.011906+00:00
-- url     : https://prove2.me/submissions/bb1ee049-6e9c-4442-be1c-3aa50ce6161a

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (P : SimpleGraph V → Prop) (hK : P K) :
    ∃ H : SimpleGraph V, K ≤ H ∧ P H ∧
      (letI : DecidableRel K.Adj := Classical.decRel K.Adj
       letI : DecidableRel H.Adj := Classical.decRel H.Adj
       ∀ G : SimpleGraph V,
         letI : DecidableRel G.Adj := Classical.decRel G.Adj
         K ≤ G → P G → G.edgeFinset.card ≤ H.edgeFinset.card) := by
  classical
  letI : DecidableEq V := Classical.decEq V
  let feasible : Finset (SimpleGraph V) :=
    Finset.univ.filter (fun G => K ≤ G ∧ P G)
  have hfeasible : feasible.Nonempty := by
    refine ⟨K, ?_⟩
    simp [feasible, hK]
  obtain ⟨H, hH, hmax⟩ :=
    Finset.exists_max_image feasible (fun G => G.edgeFinset.card) hfeasible
  refine ⟨H, ?_, ?_, ?_⟩
  · rcases Finset.mem_filter.mp hH with ⟨_, h⟩
    exact h.1
  · rcases Finset.mem_filter.mp hH with ⟨_, h⟩
    exact h.2
  · intro G hKG hPG
    apply hmax G
    simp [feasible, hKG, hPG]