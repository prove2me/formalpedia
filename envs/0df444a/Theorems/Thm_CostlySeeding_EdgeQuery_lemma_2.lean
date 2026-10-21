-- Prove2me | Theorems.Thm_CostlySeeding_EdgeQuery_lemma_2
-- name    : CostlySeeding.EdgeQuery.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:27:59.759413+00:00
-- url     : https://prove2.me/theorems/73443060-5fd8-4f15-853d-a2f276d5f9e9
-- title:
--   Lemma 2, p. 16 — initial-node sampling loss
-- statement:
--   Let $G$ have $n\ge5$ vertices, let $1\le k\le n$, let $p\in[0,1]$, and choose $\epsilon>0$, $\delta\ge2\log n$ and $0<\rho\le1$ with $\rho\ge\rho^{n,k}_{\epsilon,\delta}$ from (5). Draw $V_\rho$ uniformly among the subsets of size $\lceil n\rho\rceil$. Then
--
--   $$
--   \Pr\!\left(\forall S\subseteq V,\ |S|=k:\ |\Gamma_\rho(S)-\Gamma(S)|\le\epsilon n\right)\ge1-e^{-\delta}.
--   $$
--
--   The claim controls initial-node sampling simultaneously for all feasible seed sets.
--
--   **Formalization Note** The regime $n\ge5$, $\delta\ge2\log n$ is added to make the paper's union-bound claim valid.
-- source:
--   Eckles, Esfandiari, Mossel & Rahimian, Seeding with Costly Network Information, arXiv:1905.04325v5, p. 16, Lemma 2; pp. 35–36, B.6

import Definitions.Def_CostlySeeding_EdgeQuery_Algorithm

namespace CostlySeeding.EdgeQuery

theorem lemma_2 (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) (hn : 5 ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (eps delta rho : ℝ) (heps : 0 < eps) (hdelta : 2 * Real.log n ≤ delta)
    (hrho0 : 0 < rho) (hrho : rhoPar n k eps delta ≤ rho) (hrho1 : rho ≤ 1) :
    1 - Real.exp (-delta) ≤
      initialEventProb n (Nat.ceil ((n : ℝ) * rho)) (fun Vrho =>
        ∀ S : Finset (Fin n), S.card = k →
          |GamRho G p Vrho rho S - Gam G p S| ≤ eps * n) := by sorry

end CostlySeeding.EdgeQuery
