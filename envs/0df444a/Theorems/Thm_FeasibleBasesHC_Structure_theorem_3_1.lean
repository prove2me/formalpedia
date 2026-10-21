-- Prove2me | Theorems.Thm_FeasibleBasesHC_Structure_theorem_3_1
-- name    : FeasibleBasesHC.Structure.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:09:53.850548+00:00
-- url     : https://prove2.me/theorems/6d3ffaa6-b570-4675-ab94-b67910976d4d
-- title:
--   Theorem 3.1, p. 8 — GNF bases and good augmented forests
-- statement:
--   Let $X$ be a finite directed network with positive multipliers. Partition its arcs into basic arcs $B$, lower-bound arcs $L$, and upper-bound arcs $U$, each of which has a finite upper capacity. Then
--
--   $$(B,L,U)\text{ is a GNF basis}\quad\Longleftrightarrow\quad B\text{ is a good augmented forest spanning }V(X).$$
--
--   The theorem connects independence of GNF matrix columns to the graph structure of the basic arcs. It is the general structural result applied to the split graph in the paper.
--
--   **Formalization Note** The arc type distinguishes parallel and antiparallel arcs. A connected finite component has exactly one cycle exactly when its number of arcs equals its number of vertices. Multipliers are real and positive, covering the paper's discount factor as well as rational GNF data.
-- source:
--   Kalinowski, Mohammadian, Feasible Bases for a Polytope Related to the Hamilton Cycle Problem, arXiv:1907.12691v1, p. 8, Theorem 3.1 (citing Ahuja--Magnanti--Orlin, §15.5)

import Mathlib
import Definitions.Def_FeasibleBasesHC_Structure_Setting

namespace FeasibleBasesHC.Structure

/-- Theorem 3.1: the GNF basis theorem, including the given B,L,U partition. -/
theorem theorem_3_1 {V A : Type*} [Fintype V] [Fintype A]
    [DecidableEq V] [DecidableEq A] (N : GNF V A)
    (hmu : ∀ a ∈ N.arcs, 0 < N.mu a) (B L U : Finset A)
    (hpart : B ∪ L ∪ U = N.arcs)
    (hBL : Disjoint B L) (hBU : Disjoint B U) (hLU : Disjoint L U)
    (hUCap : ∀ a ∈ U, ∃ u, N.cap a = some u) :
    N.IsBasis B L U ↔ N.IsGoodAugForest B := by sorry

end FeasibleBasesHC.Structure
