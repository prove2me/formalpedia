-- Prove2me | Theorems.Thm_ClassifAgg_Aggregation_lemma_5
-- name    : ClassifAgg.Aggregation.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:17:50.077907+00:00
-- url     : https://prove2.me/theorems/c1cd5937-e954-4a11-b16c-a3ae7ba70e3b
-- title:
--   Lemma 5, pp. 158–159 — n^{−1/2} E d_△,e^{(1−ρ*)/2}(G_{nj*ĵ}, G_{nj*}) ≤ (3/(2√n)) E d_△^{(1−ρ*)/2}(G_{nj*ĵ}, G_{nj*}) + C n^{−κ/(2κ+ρ*−1)}
-- statement:
--   Under the hypotheses of Theorem 3, let $\hat j$ be the selected index, $G_{nkj}$ the pseudoclassifiers of the proof of Theorem 3, and $\rho^*=\rho_{j^*}$. There is $C>0$ such that for any $\pi\in\mathcal P_{j^*}$,
--   $$\frac1{\sqrt n}E_{\pi,n}\Big(d_{\triangle,e}^{(1-\rho^*)/2}(G_{nj^*\hat j},G_{nj^*})\Big)\le\frac3{2\sqrt n}E_{\pi,n}\Big(d_\triangle^{(1-\rho^*)/2}(G_{nj^*\hat j},G_{nj^*})\Big)+Cn^{-\kappa/(2\kappa+\rho^*-1)},$$
--   where $C$ does not depend on $\pi\in\mathcal P_{j^*}$.
--
--   The lemma replaces the empirical distance in the threshold $T_{nj^*}$ by the true one, at the price of a factor $3/2$ and a remainder of the optimal order.
--
--   **Formalization Note** $C$ is chosen before $n\ge1$, $j^*\in\{1,\dots,N_n\}$ and $\pi$: uniform in $j^*$ for the same reason as in Lemma 1, and in $n$ since the page names no threshold (finitely many small $n$ are absorbed into $C$, the left side being at most $1/\sqrt n$). On the event $\{\hat j>j^*\}$ the pseudoclassifier $G_{nj^*\hat j}$ is the fallback $G_{nj^*}$ (see `Procedure`). The expectations carry the hypotheses that $\{(s,x):x\in G_{nj}(s)\}$ and $\{(s,x):x\in G_{nj\hat j(s)}(s)\}$ are measurable.
-- source:
--   Tsybakov (2004), Ann. Statist. 32, Lemma 5, pp. 158–159; proof p. 159

import Mathlib
import Definitions.Def_ClassifAgg_Aggregation_Setup

namespace ClassifAgg.Aggregation

open MeasureTheory

theorem lemma_5 {d : ℕ} (S : AggSetup d) (κ ρmin ρmax β a A c0 ε0 : ℝ)
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
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ j : ℕ, 1 ≤ j → j ≤ S.N n → ∀ π ∈ S.P n j,
      1 / Real.sqrt n *
          ∫ s, dTriEmp s (Gtil n j (jhat n (S.N n) (S.net n) (S.ρ n) (Ghat n) s) s) (Ghat n j s) ^ ((1 - S.ρ n j) / 2)
            ∂(sampleLaw π.1 π.2 n)
        ≤ 3 / (2 * Real.sqrt n) *
            ∫ s, dTri π.1 (Gtil n j (jhat n (S.N n) (S.net n) (S.ρ n) (Ghat n) s) s) (Ghat n j s) ^ ((1 - S.ρ n j) / 2)
              ∂(sampleLaw π.1 π.2 n)
          + C * (n : ℝ) ^ (-κ / (2 * κ + S.ρ n j - 1)) := by sorry

end ClassifAgg.Aggregation
