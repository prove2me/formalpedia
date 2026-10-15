-- Prove2me | Theorems.Thm_FarhiQAOA_Concentration_eq_26_v2
-- name    : FarhiQAOA.Concentration.eq_26_v2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:33:13.964516+00:00
-- url     : https://prove2.me/theorems/05d89b3e-9e1a-47d5-b94e-24dc488feb4f
-- title:
--   Section II, p. 6, after (26) — for maximum degree 2, g(j,k) has at most 2p + 2 qubits
-- statement:
--   Let $G$ be a graph in which every vertex has degree at most $2$, let $p\ge0$ and let $\langle jk\rangle$ be an edge. Then the set $g(j,k)$ of qubits at graph distance at most $p$ from $j$ or from $k$ satisfies
--   $$|g(j,k)|\le 2p+2 .$$
--
--   This is the case $v=2$ of (26), which the paper states separately because the general formula has denominator $(v-1)-1=0$.
--
--   **Formalization Note** Distance is `SimpleGraph.edist`; "degree 2" is read as maximum degree at most 2, as in (26).
-- source:
--   Farhi, Goldstone, Gutmann, A Quantum Approximate Optimization Algorithm, arXiv:1411.4028v1, p. 6, Section II, after (26)

import Mathlib
import Definitions.Def_FarhiQAOA_Concentration_Setting

namespace FarhiQAOA.Concentration

theorem eq_26_v2 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hdeg : ∀ u, G.degree u ≤ 2) (p : ℕ) (j k : Fin n) (hjk : G.Adj j k) :
    (lightCone G p j k).card ≤ 2 * p + 2 := by sorry

end FarhiQAOA.Concentration
