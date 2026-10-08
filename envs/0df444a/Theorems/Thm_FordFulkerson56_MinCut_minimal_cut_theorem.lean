-- Prove2me | Theorems.Thm_FordFulkerson56_MinCut_minimal_cut_theorem
-- name    : FordFulkerson56.MinCut.minimal_cut_theorem
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T15:51:33.208165+00:00
-- url     : https://prove2.me/theorems/68d1c4b4-c428-4d21-b8f5-31b707f194e1
-- title:
--   Theorem 1 (Minimal cut theorem), p. 400 — the maximal flow value equals the minimum value of a disconnecting set
-- statement:
--   Let $N$ be a network: a finite graph whose arcs are undirected (parallel arcs allowed), with a source $a$, a sink $b\neq a$ and a positive capacity $c(e)$ on every arc. A flow sends non-negative amounts along chains (self-avoiding paths) joining $a$ and $b$, so that the total amount through each arc is at most its capacity; its value is the total amount sent. A disconnecting set is a set of arcs meeting every chain joining $a$ and $b$, and its value is $v(D)=\sum_{e\in D}c(e)$.
--
--   **Theorem (Ford–Fulkerson).** The maximal flow value obtainable in $N$ is the minimum of $v(D)$ over all disconnecting sets $D$: there is a number $m$ such that
--   $$m=\max_{f \text{ flow}}\mathrm{val}(f)=\min_{D \text{ disconnecting}} v(D),$$
--   both the maximum and the minimum being attained.
--
--   This is the max-flow min-cut theorem in its original form, for undirected networks with flows decomposed along chains.
--
--   **Formalization Note** The statement says that $m$ is the greatest element of the set of flow values and the least element of the set of values of disconnecting sets, so both extrema are attained and no supremum of a possibly empty or unbounded set is used. Flows are functions on finite sets of arcs (a collection of chain flows listing a chain twice can be merged without changing the value or any arc load).
-- source:
--   Ford & Fulkerson, Maximal Flow Through a Network, Canad. J. Math. 8 (1956), p. 400, Theorem 1 (Minimal cut theorem)

import Mathlib
import Definitions.Def_FordFulkerson56_MinCut_Network
import Definitions.Def_FordFulkerson56_MinCut_IsChain
import Definitions.Def_FordFulkerson56_MinCut_IsFlow
import Definitions.Def_FordFulkerson56_MinCut_IsDisconnecting

namespace FordFulkerson56.MinCut

theorem minimal_cut_theorem {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (N : Network V E) :
    ∃ m : ℝ, IsGreatest {x : ℝ | ∃ f, IsFlow N f ∧ value f = x} m ∧
      IsLeast {x : ℝ | ∃ D : Finset E, IsDisconnecting N D ∧ cutValue N D = x} m := by sorry

end FordFulkerson56.MinCut
