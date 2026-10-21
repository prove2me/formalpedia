-- Prove2me | Theorems.Thm_CostlySeeding_EdgeQuery_theorem_7
-- name    : CostlySeeding.EdgeQuery.theorem_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:28:02.661916+00:00
-- url     : https://prove2.me/theorems/df6ecd8b-a5f5-4589-a501-6188fe39d45d
-- title:
--   Theorem 7, p. 22 — Algorithm 4 spread and explicit expected-query guarantee
-- statement:
--   Let $G$ be an undirected simple graph on $n$ vertices, let $p\in[0,1]$, and let $1\le k\le n$. For $0<\epsilon'\le1$ and $n\ge(30/\epsilon')^2$, run Algorithm 4 with $\epsilon=\epsilon'/7$ and $\delta=2\log n$. If $\Lambda^*$ is the output seed set and $q$ is the number of PROBE edge queries, then
--
--   $$
--   \mathbb E[\Gamma(\Lambda^*)]\ge(1-1/e)\mathrm{OPT}-\epsilon'n,
--   \qquad
--   \mathbb E[q]\le Q^{n,k}_{\epsilon,\delta}+6T^{n,k}_{\epsilon,\delta}.
--   $$
--
--   The result combines near-greedy expected influence spread with the paper's explicit edge-query bound (30).
--
--   **Formalization Note** The algorithm is the paper's Algorithm 4. The query bound uses its proof's explicit formula in place of the theorem's asymptotic notation. The theorem's run-time claim requires a machine model and is outside this item. The initial sample is capped at $n$ when $\rho>1$.
-- source:
--   Eckles, Esfandiari, Mossel & Rahimian, Seeding with Costly Network Information, arXiv:1905.04325v5, p. 22, Theorem 7; p. 46, B.12, equation (30)

import Definitions.Def_CostlySeeding_EdgeQuery_Algorithm

namespace CostlySeeding.EdgeQuery

theorem theorem_7 (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (eps' : ℝ) (he0 : 0 < eps') (he1 : eps' ≤ 1)
    (hn : (30 / eps') ^ 2 ≤ (n : ℝ)) :
    (1 - Real.exp (-1)) * OPT G p k - eps' * n ≤ algSpread G p k eps' ∧
    algQueries G p k eps' ≤
      QPar n k p (eps' / 7) (2 * Real.log n) +
        6 * TPar n k (eps' / 7) (2 * Real.log n) := by sorry

end CostlySeeding.EdgeQuery
