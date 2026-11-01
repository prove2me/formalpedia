-- Prove2me | Theorems.Thm_CostlySeeding_EdgeQuery_theorem_5_fixed_initial
-- name    : CostlySeeding.EdgeQuery.theorem_5_fixed_initial
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-01T04:52:55.6278+00:00
-- url     : https://prove2.me/theorems/7880b579-2ab2-4414-87aa-77be6beaa82b
-- title:
--   Theorem 5, p. 19 — edge-query bound for a fixed initial node set with $|V_\rho|\le n\rho$
-- statement:
--   Let $G$ be an undirected simple graph on $n\ge5$ vertices, let $1\le k\le n$, $p\in[0,1]$, $0<\epsilon<1$ and $\delta\ge2\log n$. Set $\rho=\rho^{n,k}_{\epsilon,\delta}$, $T=T^{n,k}_{\epsilon,\delta}$ and $\tau=\tau^{n,k}_{\epsilon}$ as in (5), and let $Q=Q^{n,k}_{\epsilon,\delta}$ be the explicit query budget of (6)-(7), i.e.
--
--   $$
--   Q=2C^{n,k}_{\epsilon,\delta}+(2+\sqrt2)\,T\,n\sqrt{\delta+\log T}.
--   $$
--
--   Assume $\sqrt{\delta+\log T}\le n$. Fix any set $V_\rho$ of initial nodes with $|V_\rho|\le n\rho$, run $T$ independent copies of the limited probing procedure (Algorithm 2, steps 2-18) from $V_\rho$ with threshold $\tau$, and let $q$ be the total number of edge queries. Then
--
--   $$
--   \Pr\bigl(q\le Q\bigr)\ \ge\ 1-3e^{-\delta},
--   $$
--
--   the probability being over the random draws of the $T$ PROBE copies only.
--
--   This is Theorem 5 conditioned on the initial node set: the proof in Appendix B.10 treats $V_\rho$ as fixed and uses only that there are at most $n\rho$ initial nodes. The conditional form is what is needed when Algorithm 4 starts from all $n$ vertices (the case $\rho>1$).
--
--   **Formalization Note** No condition $\rho\le1$ is imposed; the initial set is an arbitrary `Finset` whose cardinality is at most $n\rho$. The probability is the exact finite weighted sum `seedEventProb` over the $T$ i.i.d. PROBE seeds, and `queries` counts all first-chance and discarded second-chance queries, as in `theorem_5`.
-- source:
--   Eckles, Esfandiari, Mossel & Rahimian, Seeding with Costly Network Information, arXiv:1905.04325v5, p. 19, Theorem 5, with quantities (5)-(7); proof in Appendix B.10, pp. 38-40 (the proof conditions on the initial set and only uses that it has at most n*rho nodes)

import Definitions.Def_CostlySeeding_EdgeQuery_Algorithm

namespace CostlySeeding.EdgeQuery

theorem theorem_5_fixed_initial (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) (hn : 5 ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (eps delta : ℝ) (heps : 0 < eps) (heps1 : eps < 1)
    (hdelta : 2 * Real.log n ≤ delta)
    (hsize : Real.sqrt (delta + Real.log (TPar n k eps delta)) ≤ n)
    (Vrho : Finset (Fin n))
    (hV : (Vrho.card : ℝ) ≤ (n : ℝ) * rhoPar n k eps delta) :
    1 - 3 * Real.exp (-delta) ≤
      seedEventProb (T := TPar n k eps delta) p (fun ss =>
          (queries G Vrho (tauPar n k eps) ss : ℝ) ≤ QPar n k p eps delta) := by sorry

end CostlySeeding.EdgeQuery
