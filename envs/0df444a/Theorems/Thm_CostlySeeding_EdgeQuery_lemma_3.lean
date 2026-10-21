-- Prove2me | Theorems.Thm_CostlySeeding_EdgeQuery_lemma_3
-- name    : CostlySeeding.EdgeQuery.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:27:54.281619+00:00
-- url     : https://prove2.me/theorems/4a20ebd9-2102-4477-8400-4124d7288eb3
-- title:
--   Lemma 3, p. 16 — probing loss
-- statement:
--   Fix an initial set $V_\rho$ of size $\lceil n\rho\rceil$ in an $n\ge5$ vertex graph, where $1\le k\le n$, $p\in[0,1]$, $\epsilon>0$, $\delta\ge2\log n$, and $\rho^{n,k}_{\epsilon,\delta}\le\rho\le1$. Generate $T\ge T^{n,k}_{\epsilon,\delta}$ independent untruncated PROBE sketches. Then
--
--   $$
--   \Pr\!\left(\forall S\subseteq V,\ |S|=k:\ |\Gamma^{(T)}_\rho(S)-\Gamma_\rho(S)|\le\epsilon n\right)\ge1-e^{-\delta}.
--   $$
--
--   This controls the error due to finite probing independently of initial-node sampling.
--
--   **Formalization Note** The inherited sample-size and sampling-rate conditions are explicit, and $n\ge5$, $\delta\ge2\log n$ are added for the union bound.
-- source:
--   Eckles, Esfandiari, Mossel & Rahimian, Seeding with Costly Network Information, arXiv:1905.04325v5, p. 16, Lemma 3; p. 36, B.7

import Definitions.Def_CostlySeeding_EdgeQuery_Algorithm

namespace CostlySeeding.EdgeQuery

theorem lemma_3 (n k T : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) (hn : 5 ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (eps delta rho : ℝ) (heps : 0 < eps) (hdelta : 2 * Real.log n ≤ delta)
    (hrho0 : 0 < rho) (hrhoPar : rhoPar n k eps delta ≤ rho)
    (hrho1 : rho ≤ 1) (hT : TPar n k eps delta ≤ T)
    (Vrho : Finset (Fin n)) (hV : Vrho.card = Nat.ceil ((n : ℝ) * rho)) :
    1 - Real.exp (-delta) ≤
      seedEventProb (T := T) p (fun ss =>
        ∀ S : Finset (Fin n), S.card = k →
          |GamUncut G Vrho rho ss S - GamRho G p Vrho rho S| ≤ eps * n) := by sorry

end CostlySeeding.EdgeQuery
