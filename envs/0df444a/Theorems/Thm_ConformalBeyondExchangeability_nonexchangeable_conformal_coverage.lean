-- Prove2me | Theorems.Thm_ConformalBeyondExchangeability_nonexchangeable_conformal_coverage
-- name    : ConformalBeyondExchangeability.nonexchangeable_conformal_coverage
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T07:48:59.805014+00:00
-- url     : https://prove2.me/theorems/7c984d03-a287-418b-9a05-13529e170b8d
-- title:
--   Theorem 2: nonexchangeable full and split conformal prediction
-- statement:
--   Let the data $Z=((X_1,Y_1),\dots,(X_{n+1},Y_{n+1}))$ have an arbitrary joint law $P$. Let $w_1,\dots,w_n\in[0,1]$ be fixed weights with normalized weights $\tilde w_i$ (eq. (10)), and let $\alpha\in(0,1)$.
--
--   1. **Full conformal.** Let $\mathcal A$ be an algorithm on tagged data points with fixed tags $t_1,\dots,t_{n+1}$ (eq. (16)), such that the residual map $z\mapsto R(z)$, $R(z)_i=|y_i-\hat\mu(x_i)|$ with $\hat\mu=\mathcal A((x_i,y_i,t_i):i\in[n+1])$, is measurable. Let $\hat C_n$ be the nonexchangeable full conformal set (eq. (18)), built with the random index $K\sim\sum_i\tilde w_i\delta_i$ drawn independently of $Z$. Then
--   $$P\{Y_{n+1}\in\hat C_n(X_{n+1})\}\ge1-\alpha-\sum_{i=1}^n\tilde w_i\cdot\mathsf d_{\mathsf{TV}}\big(R(Z),R(Z^i)\big).$$
--   2. **Split conformal.** For a measurable pre-fitted $\hat\mu$ and the interval of eq. (11), the same bound holds with $R(Z)_i=|Y_i-\hat\mu(X_i)|$, $i=1,\dots,n+1$.
--
--   The coverage gap is bounded by the total variation between the residual vectors before and after swapping the test point with each training point. It vanishes for exchangeable data, for any weights and any algorithm.
--
--   **Formalization Note** The probability over $(Z,K)$ is written as $\sum_k\tilde w_k\,P\{Y_{n+1}\in\hat C^{(k)}_n(X_{n+1})\}$, where $\hat C^{(k)}_n$ is the set built with $K=k$. The paper requires each fitted $\hat\mu$ to be measurable. The statement assumes the residual map $z\mapsto R(z)$ is measurable, which makes $R(Z)$ a random vector and its total variation distances defined. The miscoverage level $\alpha\in(0,1)$ is the paper's implicit range.
-- source:
--   Barber, Candès, Ramdas and Tibshirani, Conformal prediction beyond exchangeability, arXiv:2202.13415v5 (2023), Section 4.1, Theorem 2, eqs. (11), (17), (18), p. 15; proof in Section 6.2, pp. 30-31

import Mathlib
import Definitions.Def_ConformalBeyondExchangeability_Basic

open MeasureTheory

namespace ConformalBeyondExchangeability

theorem nonexchangeable_conformal_coverage {X T : Type*} [MeasurableSpace X] {n : ℕ}
    (P : Measure (Fin (n + 1) → X × ℝ)) [IsProbabilityMeasure P]
    (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    (∀ (alg : TaggedAlg X T) (t : Fin (n + 1) → T), Measurable (residuals alg t) →
      1 - α - swapGap P w (residuals alg t) ≤ fullCoverage P alg t w α) ∧
    (∀ μ : X → ℝ, Measurable μ →
      1 - α - swapGap P w (splitResiduals μ) ≤ splitCoverage P μ w α) := by sorry

end ConformalBeyondExchangeability
