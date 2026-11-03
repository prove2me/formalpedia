-- Prove2me | solution 1 for maximal_planar_edge_count__p2m_10eaf2f1_7409_4fae_95fa_e1e70a835601_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T11:17:30.632085+00:00
-- url     : https://prove2.me/submissions/8e268c3b-8fb9-4c30-848f-b3152ac5aa08

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_has_euler_edge_count
import Theorems.Thm_CompactnessConjecture_edgeFinset_card_eq_natCard

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (dM : DecidableRel M.Adj)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ (N : SimpleGraph V),
      M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) :
    M.edgeFinset.card = 3 * Fintype.card V - 6 := by
  have hMax' : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N ≤ M := hMax
  have hEuler : M.edgeSet.ncard + 6 = 3 * Fintype.card V :=
    WilliamsonShmoys.maximal_drawable_graph_has_euler_edge_count
      M hM hV hMax'
  have hCard : M.edgeFinset.card = M.edgeSet.ncard := by
    change M.edgeFinset.card = Nat.card M.edgeSet
    exact CompactnessConjecture.edgeFinset_card_eq_natCard M
  have hEq : M.edgeFinset.card + 6 = 3 * Fintype.card V := by
    calc
      M.edgeFinset.card + 6 = M.edgeSet.ncard + 6 := by rw [hCard]
      _ = 3 * Fintype.card V := hEuler
  calc
    M.edgeFinset.card = (M.edgeFinset.card + 6) - 6 := by omega
    _ = 3 * Fintype.card V - 6 := by rw [hEq]
