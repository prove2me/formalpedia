-- Prove2me | Theorems.Thm_ClassifAgg_Aggregation_lemma_1
-- name    : ClassifAgg.Aggregation.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:17:52.289014+00:00
-- url     : https://prove2.me/theorems/2148625f-9e04-4037-b9b7-91c9161bfb5c
-- title:
--   Lemma 1, p. 152 — sup_{π∈𝒫_{j*}} P_{π,n}(ĵ > j*) = o(1/n)
-- statement:
--   Under the hypotheses of Theorem 3 (assumptions (A3), (A4), $N=O(n^\beta)$, $\mathcal P_j$ being $(\mathcal G_j,\kappa,\rho_j)$-classes), let $\hat j$ be the index selected by the aggregation procedure from empirical risk minimizers $G_{nk}$ over $\mathcal N_k$. For an index $j^*$ and $\pi\in\mathcal P_{j^*}$ (so that $G^*_\pi\in\mathcal G_{j^*}$),
--   $$\sup_{\pi\in\mathcal P_{j^*}}P_{\pi,n}(\hat j>j^*)=o(1/n),\qquad n\to\infty.$$
--
--   That is, with probability close to $1$ the true index $j^*$ is admissible, so the procedure never selects a class that is too rich.
--
--   **Formalization Note** "$=o(1/n)$" is written as: for every $\varepsilon>0$ there is $N_0$ such that for all $n\ge N_0$, every $j^*\in\{1,\dots,N_n\}$ and every $\pi\in\mathcal P_{j^*}$, the probability is at most $\varepsilon/n$. The threshold is uniform in $j^*$ because in the setting of Section 3 the indices, classes and complexities move with $n$, and the proof of Theorem 3 needs the bound uniformly. The probability is the outer measure of the event. The setup hypotheses are those of the goal theorem (see the definition `Setup`).
-- source:
--   Tsybakov (2004), Ann. Statist. 32, Lemma 1, p. 152; proof pp. 155–158

import Mathlib
import Definitions.Def_ClassifAgg_Aggregation_Setup

namespace ClassifAgg.Aggregation

open MeasureTheory

theorem lemma_1 {d : ℕ} (S : AggSetup d) (κ ρmin ρmax β a A c0 ε0 : ℝ)
    (hS : AggAssumptions S κ ρmin ρmax β a A c0 ε0)
    (Ghat : (n : ℕ) → ℕ → (Fin n → E d × Bool) → Set (E d))
    (hERM : ∀ n k, 1 ≤ k → k ≤ S.N n → IsERM (S.net n k) (Ghat n k)) :
    ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n → ∀ j : ℕ, 1 ≤ j → j ≤ S.N n →
      ∀ π ∈ S.P n j,
        sampleLaw π.1 π.2 n {s | j < jhat n (S.N n) (S.net n) (S.ρ n) (Ghat n) s}
          ≤ ENNReal.ofReal (ε / n) := by sorry

end ClassifAgg.Aggregation
