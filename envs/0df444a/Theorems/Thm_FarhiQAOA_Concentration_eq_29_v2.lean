-- Prove2me | Theorems.Thm_FarhiQAOA_Concentration_eq_29_v2
-- name    : FarhiQAOA.Concentration.eq_29_v2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:33:13.678984+00:00
-- url     : https://prove2.me/theorems/d3b0e193-1055-4235-bcff-5bb12d0e8991
-- title:
--   Section III, p. 7, after (29) — for maximum degree 2, at most 4p + 4 edges have g(j′,k′) meeting g(j,k)
-- statement:
--   Let $G$ be a graph in which every vertex has degree at most $2$, let $p\ge0$ and let $\langle jk\rangle$ be an edge. With $g(\cdot,\cdot)$ the set of qubits within graph distance $p$ of an edge's endpoints,
--   $$\#\{\langle j'k'\rangle : g(j,k)\cap g(j',k')\ne\emptyset\}\le 4p+4,$$
--   edges counted once each, $\langle jk\rangle$ included.
--
--   This is the case $v=2$ of (29), stated separately in the paper.
--
--   **Formalization Note** As in `eq_29`, "could contribute to the sum in (28)" is formalized as "the subgraphs share a qubit". Distance is `SimpleGraph.edist`.
-- source:
--   Farhi, Goldstone, Gutmann, A Quantum Approximate Optimization Algorithm, arXiv:1411.4028v1, p. 7, Section III, after (29)

import Mathlib
import Definitions.Def_FarhiQAOA_Concentration_Setting

namespace FarhiQAOA.Concentration

theorem eq_29_v2 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hdeg : ∀ u, G.degree u ≤ 2) (p : ℕ) (j k : Fin n) (hjk : G.Adj j k) :
    ((edgePairs G).filter fun e =>
        ¬ Disjoint (lightCone G p j k) (lightCone G p e.1 e.2)).card ≤ 4 * p + 4 := by sorry

end FarhiQAOA.Concentration
