-- Prove2me | Theorems.Thm_ClassifAgg_Aggregation_lemma_3
-- name    : ClassifAgg.Aggregation.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:17:47.263979+00:00
-- url     : https://prove2.me/theorems/d616681b-8f49-45fe-8403-37584fd465e7
-- title:
--   Lemma 3, p. 153 — sup_{π∈𝒫_{j*}} n^{−1/2} E d_△^{(1−ρ*)/2}(G_{nj*}, G*) = O(n^{−κ/(2κ+ρ*−1)})
-- statement:
--   Under the hypotheses of Theorem 3, let $G_{nj^*}$ be the empirical risk minimizer over $\mathcal N_{j^*}$ and $\rho^*=\rho_{j^*}$. Then
--   $$\sup_{\pi\in\mathcal P_{j^*}}\frac1{\sqrt n}E_{\pi,n}\Big(d_\triangle^{(1-\rho^*)/2}(G_{nj^*},G^*)\Big)=O\big(n^{-\kappa/(2\kappa+\rho^*-1)}\big),\qquad n\to\infty.$$
--
--   It bounds the size of the fluctuation term that appears when the adaptive classifier is compared with $G_{nj^*}$.
--
--   **Formalization Note** "$=O(\cdot)$ as $n\to\infty$" is written with one constant $C$ and one threshold $N_0$, uniform in $j^*\in\{1,\dots,N_n\}$ and $\pi\in\mathcal P_{j^*}$. The expectation carries the hypothesis that $\{(s,x):x\in G_{nj}(s)\}$ is measurable for every $j$; without it the integral of a non-measurable integrand would be $0$.
-- source:
--   Tsybakov (2004), Ann. Statist. 32, Lemma 3, p. 153; proof p. 158

import Mathlib
import Definitions.Def_ClassifAgg_Aggregation_Setup

namespace ClassifAgg.Aggregation

open MeasureTheory

theorem lemma_3 {d : ℕ} (S : AggSetup d) (κ ρmin ρmax β a A c0 ε0 : ℝ)
    (hS : AggAssumptions S κ ρmin ρmax β a A c0 ε0)
    (Ghat : (n : ℕ) → ℕ → (Fin n → E d × Bool) → Set (E d))
    (hERM : ∀ n k, 1 ≤ k → k ≤ S.N n → IsERM (S.net n k) (Ghat n k))
    (hmeasG : ∀ n j, 1 ≤ j → j ≤ S.N n →
      MeasurableSet {p : (Fin n → E d × Bool) × E d | p.2 ∈ Ghat n j p.1}) :
    ∃ C : ℝ, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n → ∀ j : ℕ, 1 ≤ j → j ≤ S.N n → ∀ π ∈ S.P n j,
      1 / Real.sqrt n *
          ∫ s, dTri π.1 (Ghat n j s) (bayesSet π.2) ^ ((1 - S.ρ n j) / 2)
            ∂(sampleLaw π.1 π.2 n)
        ≤ C * (n : ℝ) ^ (-κ / (2 * κ + S.ρ n j - 1)) := by sorry

end ClassifAgg.Aggregation
