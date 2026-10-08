-- Prove2me | Theorems.Thm_ClassifAgg_Aggregation_lemma_6
-- name    : ClassifAgg.Aggregation.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:17:38.431522+00:00
-- url     : https://prove2.me/theorems/4dfb25e4-edef-4bf0-9a24-3171a2837762
-- title:
--   Lemma 6, p. 161 — sup_{π∈𝒫_{j*}} P_{π,n}(d_△(G_{nj*ĵ}, G*) ≥ ε₀) = O(n^{−κ/(2κ+ρ*−1)})
-- statement:
--   Under the hypotheses of Theorem 3, let $\varepsilon_0$ be the constant from assumption (A1), $\hat j$ the selected index, $G_{nkj}$ the pseudoclassifiers of the proof of Theorem 3 and $\rho^*=\rho_{j^*}$. Then
--   $$\sup_{\pi\in\mathcal P_{j^*}}P_{\pi,n}\big(d_\triangle(G_{nj^*\hat j},G^*)\ge\varepsilon_0\big)=O\big(n^{-\kappa/(2\kappa+\rho^*-1)}\big),\qquad n\to\infty.$$
--
--   With high probability the pseudoclassifier lies in the region where the margin assumption (A1) applies.
--
--   **Formalization Note** "$=O(\cdot)$" is written with one constant $C$ and one threshold $N_0$, uniform in $j^*\in\{1,\dots,N_n\}$ and $\pi\in\mathcal P_{j^*}$. The probability is the outer measure of the event.
-- source:
--   Tsybakov (2004), Ann. Statist. 32, Lemma 6, p. 161; proof pp. 161–162

import Mathlib
import Definitions.Def_ClassifAgg_Aggregation_Setup

namespace ClassifAgg.Aggregation

open MeasureTheory

theorem lemma_6 {d : ℕ} (S : AggSetup d) (κ ρmin ρmax β a A c0 ε0 : ℝ)
    (hS : AggAssumptions S κ ρmin ρmax β a A c0 ε0)
    (Ghat : (n : ℕ) → ℕ → (Fin n → E d × Bool) → Set (E d))
    (hERM : ∀ n k, 1 ≤ k → k ≤ S.N n → IsERM (S.net n k) (Ghat n k))
    (Gtil : (n : ℕ) → ℕ → ℕ → (Fin n → E d × Bool) → Set (E d))
    (hsel : ∀ n, IsPseudoSel n (S.net n) (S.ρ n) (Ghat n) (Gtil n)) :
    ∃ C : ℝ, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n → ∀ j : ℕ, 1 ≤ j → j ≤ S.N n → ∀ π ∈ S.P n j,
      sampleLaw π.1 π.2 n
          {s | ε0 ≤ dTri π.1 (Gtil n j (jhat n (S.N n) (S.net n) (S.ρ n) (Ghat n) s) s) (bayesSet π.2)}
        ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-κ / (2 * κ + S.ρ n j - 1))) := by sorry

end ClassifAgg.Aggregation
