-- Prove2me | Theorems.Thm_ClassifAgg_Aggregation_lemma_4
-- name    : ClassifAgg.Aggregation.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:17:57.275085+00:00
-- url     : https://prove2.me/theorems/bbf46f26-9841-485f-9d69-64f2b1a91838
-- title:
--   Lemma 4, p. 153 — sup_{π∈𝒫_{j*}} E T_{nj*}(G_{nj*ĵ}, G_{nj*}) = O((log n)^{4κ/(2κ+ρ*−1)} n^{−κ/(2κ+ρ*−1)})
-- statement:
--   Under the hypotheses of Theorem 3, let $\hat j$ be the selected index, $G_{nkj}$ the pseudoclassifiers of the proof of Theorem 3, $T_{nk}$ the thresholds of the procedure, and $\rho^*=\rho_{j^*}$. Then
--   $$\sup_{\pi\in\mathcal P_{j^*}}E_{\pi,n}\big(T_{nj^*}(G_{nj^*\hat j},G_{nj^*})\big)=O\Big((\log n)^{4\kappa/(2\kappa+\rho^*-1)}n^{-\kappa/(2\kappa+\rho^*-1)}\Big),\qquad n\to\infty.$$
--
--   The expected threshold between the pseudoclassifier and the oracle classifier $G_{nj^*}$ is of the target order; this is the last ingredient of the proof of Theorem 3.
--
--   **Formalization Note** "$=O(\cdot)$" is written with one constant $C$ and one threshold $N_0$, uniform in $j^*\in\{1,\dots,N_n\}$ and $\pi\in\mathcal P_{j^*}$. The expectation carries the measurability hypotheses of Lemma 5.
-- source:
--   Tsybakov (2004), Ann. Statist. 32, Lemma 4, p. 153; proof pp. 159–162

import Mathlib
import Definitions.Def_ClassifAgg_Aggregation_Setup

namespace ClassifAgg.Aggregation

open MeasureTheory

theorem lemma_4 {d : ℕ} (S : AggSetup d) (κ ρmin ρmax β a A c0 ε0 : ℝ)
    (hS : AggAssumptions S κ ρmin ρmax β a A c0 ε0)
    (Ghat : (n : ℕ) → ℕ → (Fin n → E d × Bool) → Set (E d))
    (hERM : ∀ n k, 1 ≤ k → k ≤ S.N n → IsERM (S.net n k) (Ghat n k))
    (Gtil : (n : ℕ) → ℕ → ℕ → (Fin n → E d × Bool) → Set (E d))
    (hsel : ∀ n, IsPseudoSel n (S.net n) (S.ρ n) (Ghat n) (Gtil n))
    (hmeasG : ∀ n j, 1 ≤ j → j ≤ S.N n →
      MeasurableSet {p : (Fin n → E d × Bool) × E d | p.2 ∈ Ghat n j p.1})
    (hmeasT : ∀ n j, 1 ≤ j → j ≤ S.N n →
      MeasurableSet {p : (Fin n → E d × Bool) × E d |
        p.2 ∈ Gtil n j (jhat n (S.N n) (S.net n) (S.ρ n) (Ghat n) p.1) p.1}) :
    ∃ C : ℝ, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n → ∀ j : ℕ, 1 ≤ j → j ≤ S.N n → ∀ π ∈ S.P n j,
      ∫ s, threshold n (S.ρ n j) (Gtil n j (jhat n (S.N n) (S.net n) (S.ρ n) (Ghat n) s) s) (Ghat n j s) s
          ∂(sampleLaw π.1 π.2 n)
        ≤ C * Real.log n ^ (4 * κ / (2 * κ + S.ρ n j - 1))
            * (n : ℝ) ^ (-κ / (2 * κ + S.ρ n j - 1)) := by sorry

end ClassifAgg.Aggregation
