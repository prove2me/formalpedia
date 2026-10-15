-- Prove2me | Theorems.Thm_FarhiQAOA_Concentration_eq_29
-- name    : FarhiQAOA.Concentration.eq_29
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:33:24.847838+00:00
-- url     : https://prove2.me/theorems/95a7a1af-afae-43e6-b53c-88bb725cf541
-- title:
--   Section III, (29), p. 7 — at most 2[((v−1)^{2p+2}−1)/((v−1)−1)] edges ⟨j′k′⟩ have g(j′,k′) meeting g(j,k)
-- statement:
--   Let $G$ be a graph of maximum degree at most $v$, where $v\ge3$, let $p\ge0$, and let $\langle jk\rangle$ be an edge. For an edge $\langle j'k'\rangle$ let $g(j',k')$ be the set of qubits at graph distance at most $p$ from $j'$ or $k'$. The number of edges $\langle j'k'\rangle$ (counted once each, $\langle jk\rangle$ itself included) whose subgraph shares a qubit with $g(j,k)$ satisfies
--   $$\#\{\langle j'k'\rangle : g(j,k)\cap g(j',k')\ne\emptyset\} \le 2\left[\frac{(v-1)^{2p+2}-1}{(v-1)-1}\right].$$
--
--   These are the edges which could contribute to the sum in (28) together with $\langle jk\rangle$: by the disjointness statement, every other summand vanishes. The bound is independent of $n$ and $m$.
--
--   **Formalization Note** "Could contribute" is formalized as "the subgraphs share a qubit", the complement of the hypothesis under which a summand is zero. The paper's sufficient condition (no path of length $2p+1$ or shorter between the edges) is how it counts, not part of the claim. The case $v=2$ (bound $4p+4$) is `eq_29_v2`. Distance is `SimpleGraph.edist`.
-- source:
--   Farhi, Goldstone, Gutmann, A Quantum Approximate Optimization Algorithm, arXiv:1411.4028v1, p. 7, Section III, (29)

import Mathlib
import Definitions.Def_FarhiQAOA_Concentration_Setting

namespace FarhiQAOA.Concentration

theorem eq_29 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : ℕ) (hv : 3 ≤ v)
    (hdeg : ∀ u, G.degree u ≤ v) (p : ℕ) (j k : Fin n) (hjk : G.Adj j k) :
    (((edgePairs G).filter fun e =>
        ¬ Disjoint (lightCone G p j k) (lightCone G p e.1 e.2)).card : ℝ) ≤
      2 * ((((v : ℝ) - 1) ^ (2 * p + 2) - 1) / (((v : ℝ) - 1) - 1)) := by sorry

end FarhiQAOA.Concentration
