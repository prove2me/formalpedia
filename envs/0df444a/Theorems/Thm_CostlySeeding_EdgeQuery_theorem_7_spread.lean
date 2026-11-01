-- Prove2me | Theorems.Thm_CostlySeeding_EdgeQuery_theorem_7_spread
-- name    : CostlySeeding.EdgeQuery.theorem_7_spread
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-01T04:52:56.699965+00:00
-- url     : https://prove2.me/theorems/a2293609-5e9a-4646-b391-1684a450075f
-- title:
--   Theorem 7, p. 22 — spread guarantee of Algorithm 4: $\mathbb E[\Gamma(\Lambda^*)]\ge(1-1/e)\mathrm{OPT}-\epsilon' n$
-- statement:
--   Let $G$ be an undirected simple graph on $n$ vertices, let $p\in[0,1]$ be the independent-cascade probability, and let $1\le k\le n$. For a seed set $S$, $\Gamma(S)$ is the expected number of vertices reached from $S$ when every edge is kept independently with probability $p$, and $\mathrm{OPT}=\max_{|S|=k}\Gamma(S)$.
--
--   Fix $0<\epsilon'\le 1$ with $n\ge(30/\epsilon')^2$ and run Algorithm 4: PROBE with $\epsilon=\epsilon'/7$, $\delta=2\log n$, $\rho=\rho^{n,k}_{\epsilon,\delta}$, $T=T^{n,k}_{\epsilon,\delta}$ and $\tau=\tau^{n,k}_{\epsilon}$ from (5), followed by the stochastic greedy SEED$(\epsilon,k)$ on the truncated sketch $\Gamma^{(T)}_{\rho,\tau}$. If $\Lambda^*$ is the returned seed set, then
--
--   $$
--   \mathbb E\bigl[\Gamma(\Lambda^*)\bigr]\ \ge\ (1-1/e)\,\mathrm{OPT}-\epsilon' n,
--   $$
--
--   where the expectation is over the initial nodes, the $T$ PROBE copies and the randomness of SEED.
--
--   This is the approximation half of Theorem 7; the expected-query half of Theorem 7 follows from Theorem 5 and the worst-case count $2Tn^2$, as in equation (30).
--
--   **Formalization Note** The statement is the first conjunct of `CostlySeeding.EdgeQuery.theorem_7`, with the same definitions (`algSpread` is the exact expectation of $\Gamma(\Lambda^*)$ under Algorithm 4). When $\rho>1$ the initial sample is capped at all $n$ vertices, exactly as in `theorem_7`.
-- source:
--   Eckles, Esfandiari, Mossel & Rahimian, Seeding with Costly Network Information, arXiv:1905.04325v5, p. 22, Theorem 7 (influence-spread claim); proof in Appendix B.12, pp. 46

import Definitions.Def_CostlySeeding_EdgeQuery_Algorithm

namespace CostlySeeding.EdgeQuery

theorem theorem_7_spread (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (eps' : ℝ) (he0 : 0 < eps') (he1 : eps' ≤ 1)
    (hn : (30 / eps') ^ 2 ≤ (n : ℝ)) :
    (1 - Real.exp (-1)) * OPT G p k - eps' * n ≤ algSpread G p k eps' := by sorry

end CostlySeeding.EdgeQuery
