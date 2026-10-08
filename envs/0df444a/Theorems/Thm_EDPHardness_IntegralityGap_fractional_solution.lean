-- Prove2me | Theorems.Thm_EDPHardness_IntegralityGap_fractional_solution
-- name    : EDPHardness.IntegralityGap.fractional_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:07:50.964235+00:00
-- url     : https://prove2.me/theorems/bab63162-8002-4c2d-b1cf-9c4e32d5d0d9
-- title:
--   §2.4 ¶2 — 1/c on every canonical path is a feasible fractional solution of value n/c
-- statement:
--   Let $c\ge2$ and let $H$ be any hypergraph on $n$ vertices with $\lfloor\beta_2n\rfloor$ hyperedges of size $c$, and $G(H)$ the EDP instance built from it, with pairs $(s(v),t(v))$ and canonical paths $P(v)$.
--
--   Sending $1/c$ units of flow on each canonical path is a feasible solution of the multicommodity flow relaxation (every edge carries at most one unit), and its value is
--   $$\sum_{v} x_v=\frac nc .$$
--   Precisely: there is a feasible fractional solution of value $n/c$ whose flow-carrying paths are canonical paths, each carrying $1/c$.
--
--   This is the fractional side of the integrality gap: the LP optimum of $G(H)$ is at least $n/c$ for every $H$.
--
--   **Formalization Note** A flow-carrying path is identified as canonical by its vertex sequence. The statement holds for every $H$ (no randomness is needed); a vertex in no hyperedge has the canonical path $(s(v),t(v))$ by the convention of the definitions.
-- source:
--   Andrews, Chuzhoy, Guruswami, Khanna, Talwar, Zhang, Inapproximability of Edge-Disjoint Paths and Low Congestion Routing on Undirected Graphs, Combinatorica 30 (2010), p. 495, Section 2.4, second paragraph

import Mathlib
import Definitions.Def_EDPHardness_IntegralityGap_FlowRelaxation
import Definitions.Def_EDPHardness_IntegralityGap_GapInstance

namespace EDPHardness.IntegralityGap

theorem fractional_solution (n c : ℕ) (hc : 2 ≤ c) (H : Hyp n (numEdges n c) c) :
    ∃ F : FracSol (gapGraph H) (src n (numEdges n c)) (snk n (numEdges n c)),
      F.value = (n : ℝ) / c ∧
      ∀ v, ∀ P ∈ F.paths v, P.support = canonicalSupport H v ∧ F.f v P = 1 / (c : ℝ) := by sorry

end EDPHardness.IntegralityGap
