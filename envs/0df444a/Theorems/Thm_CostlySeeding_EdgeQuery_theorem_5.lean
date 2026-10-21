-- Prove2me | Theorems.Thm_CostlySeeding_EdgeQuery_theorem_5
-- name    : CostlySeeding.EdgeQuery.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:27:59.945097+00:00
-- url     : https://prove2.me/theorems/0a28068a-e3f5-4f2b-a8bc-d723e17b2514
-- title:
--   Theorem 5, p. 19 — high-probability edge-query bound
-- statement:
--   Run PROBE with $\rho=\rho^{n,k}_{\epsilon,\delta}$, $T=T^{n,k}_{\epsilon,\delta}$, and $\tau=\tau^{n,k}_\epsilon$ from (5), and let $q$ count all edge queries. Suppose $n\ge5$, $1\le k\le n$, $p\in[0,1]$, $0<\epsilon<1$, $\delta\ge2\log n$, $\rho\le1$, and $n\ge\sqrt{\delta+\log T}$. Then
--
--   $$
--   \Pr\!\left(q\le Q^{n,k}_{\epsilon,\delta}\right)\ge1-3e^{-\delta},
--   $$
--
--   with the exact $Q$ of (6)–(7). This is the paper's main high-probability bound on PROBE's edge-query count.
--
--   **Formalization Note** The regime $n\ge5$, $\delta\ge2\log n$ and the feasible sample-rate condition $\rho\le1$ are explicit additions. The printed theorem's unused $\alpha$ is omitted.
-- source:
--   Eckles, Esfandiari, Mossel & Rahimian, Seeding with Costly Network Information, arXiv:1905.04325v5, p. 19, Theorem 5; pp. 38–40, B.10

import Definitions.Def_CostlySeeding_EdgeQuery_Algorithm

namespace CostlySeeding.EdgeQuery

theorem theorem_5 (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) (hn : 5 ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (eps delta : ℝ) (heps : 0 < eps) (heps1 : eps < 1)
    (hdelta : 2 * Real.log n ≤ delta)
    (hrho : rhoPar n k eps delta ≤ 1)
    (hsize : Real.sqrt (delta + Real.log (TPar n k eps delta)) ≤ n) :
    1 - 3 * Real.exp (-delta) ≤
      probeEventProb (T := TPar n k eps delta) p
        (Nat.ceil ((n : ℝ) * rhoPar n k eps delta)) (fun Vrho ss =>
          (queries G Vrho (tauPar n k eps) ss : ℝ) ≤ QPar n k p eps delta) := by sorry

end CostlySeeding.EdgeQuery
