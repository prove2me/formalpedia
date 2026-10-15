-- Prove2me | Theorems.Thm_FarhiQAOA_Concentration_eq_26
-- name    : FarhiQAOA.Concentration.eq_26
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:33:12.146836+00:00
-- url     : https://prove2.me/theorems/c5202816-035d-43e7-9473-784f4856a413
-- title:
--   Section II, (26), p. 6 — g(j,k) has at most 2[((v−1)^{p+1}−1)/((v−1)−1)] qubits when the maximum degree is v
-- statement:
--   Let $G$ be a graph of maximum degree at most $v$, where $v\ge 3$, let $p\ge0$, and let $\langle jk\rangle$ be an edge of $G$. Let $g(j,k)$ be the set of qubits at graph distance at most $p$ from $j$ or from $k$. Then
--   $$|g(j,k)| \le q_{\text{tree}} = 2\left[\frac{(v-1)^{p+1}-1}{(v-1)-1}\right].$$
--
--   The right side is the number of qubits of the subgraph when it is a tree, which the paper identifies as the maximum; it is independent of $n$ and $m$, which is what makes $F_p$ classically computable and the concentration estimate (29)–(30) possible.
--
--   **Formalization Note** "Maximum degree $v$" is the hypothesis that every vertex has degree at most $v$. The case $v=2$, where the printed fraction is $0/0$, is the separate statement `eq_26_v2` (bound $2p+2$). Distance is `SimpleGraph.edist`. The paper prints (26) as the size of the tree; the statement formalizes its use as an upper bound on $|g(j,k)|$ for every graph of maximum degree $v$.
-- source:
--   Farhi, Goldstone, Gutmann, A Quantum Approximate Optimization Algorithm, arXiv:1411.4028v1, p. 6, Section II, (26)

import Mathlib
import Definitions.Def_FarhiQAOA_Concentration_Setting

namespace FarhiQAOA.Concentration

theorem eq_26 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : ℕ) (hv : 3 ≤ v)
    (hdeg : ∀ u, G.degree u ≤ v) (p : ℕ) (j k : Fin n) (hjk : G.Adj j k) :
    ((lightCone G p j k).card : ℝ) ≤
      2 * ((((v : ℝ) - 1) ^ (p + 1) - 1) / (((v : ℝ) - 1) - 1)) := by sorry

end FarhiQAOA.Concentration
