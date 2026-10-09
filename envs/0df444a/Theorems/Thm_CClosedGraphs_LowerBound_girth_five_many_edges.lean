-- Prove2me | Theorems.Thm_CClosedGraphs_LowerBound_girth_five_many_edges
-- name    : CClosedGraphs.LowerBound.girth_five_many_edges
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:22:47.915008+00:00
-- url     : https://prove2.me/theorems/fe4356b2-155f-43ca-97f1-2e73539b11f5
-- title:
--   §4, p. 12 (cites [29]) — there are graphs on v vertices with girth at least 5 and Ω(v^{3/2}) edges
-- statement:
--   There is an absolute constant $C > 0$ such that for every integer $v \ge 2$ there is a graph $H$ on $v$ vertices whose girth is at least $5$ (it contains no triangle and no $4$-cycle) and whose number of edges satisfies
--   $$
--   |E(H)| \ \ge\ C\, v^{3/2} .
--   $$
--
--   This is the classical lower bound for the Turán number of the $4$-cycle (Erdős–Rényi–Sós and Brown, via polarity graphs of projective planes; surveyed by Füredi and Simonovits [29]). The paper uses it as the base graph $H$ of its lower-bound construction.
--
--   **Formalization Note** Girth is Mathlib's `egirth`, valued in $\mathbb N \cup \{\infty\}$ and equal to $\infty$ for acyclic graphs, so "girth $\ge 5$" admits forests. The paper speaks of the graph "with girth 5 and the maximum possible number of edges, which is $\Omega(v^{3/2})$"; only the lower bound is used, and that is what is stated. The hypothesis $v \ge 2$ is needed because a graph on one vertex has no edge.
-- source:
--   Fox, Roughgarden, Seshadhri, Wei and Wein, Finding cliques in social networks: a new distribution-free model, arXiv:1804.07431v1, p. 12, §4, Construction (citing [29], Füredi–Simonovits)

import Mathlib
import Definitions.Def_CClosedGraphs_LowerBound_Setting

namespace CClosedGraphs.LowerBound
theorem girth_five_many_edges : ∃ C : ℝ, 0 < C ∧ ∀ v : ℕ, 2 ≤ v →
    ∃ H : SimpleGraph (Fin v), 5 ≤ H.egirth ∧
      C * (v : ℝ) ^ ((3 : ℝ) / 2) ≤ (H.edgeSet.ncard : ℝ) := by sorry
end CClosedGraphs.LowerBound
