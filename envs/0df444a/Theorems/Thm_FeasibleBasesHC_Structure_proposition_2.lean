-- Prove2me | Theorems.Thm_FeasibleBasesHC_Structure_proposition_2
-- name    : FeasibleBasesHC.Structure.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:09:54.813954+00:00
-- url     : https://prove2.me/theorems/61476fdb-04a4-417c-b608-fc5a1fccc12d
-- title:
--   Proposition 2, p. 8 — breakeven cycles are balanced
-- statement:
--   Let $C$ be an oriented undirected cycle in the split graph $G'$, with multiplier $\mu(C)$ and counts of forward and backward arcs. For $0<\beta<1$,
--
--   $$\mu(C)=1\quad\Longleftrightarrow\quad |C^+|=|C^-|.$$
--
--   Thus the numerical breakeven condition for a GNF cycle becomes a combinatorial balance condition in this graph.
--
--   **Formalization Note** Paper node $1$ is `0 : Fin n`; `[NeZero n]` ensures it exists. Cycle orientation is represented by an ordered list of distinct arc occurrences.
-- source:
--   Kalinowski, Mohammadian, Feasible Bases for a Polytope Related to the Hamilton Cycle Problem, arXiv:1907.12691v1, p. 8, Proposition 2

import Mathlib
import Definitions.Def_FeasibleBasesHC_Structure_Setting

namespace FeasibleBasesHC.Structure

/-- Proposition 2: in the split graph breakeven and balance coincide. -/
theorem proposition_2 {n : ℕ} [NeZero n] (G : Digraph n)
    (beta : ℝ) (hpos : 0 < beta) (hlt : beta < 1)
    (C : (Gp G beta).Cycle) :
    C.multiplier = 1 ↔ C.Balanced := by sorry

end FeasibleBasesHC.Structure
