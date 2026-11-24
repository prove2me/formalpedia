-- Prove2me | Theorems.Thm_ConformalBeyondExchangeability_nonexchangeable_conformal_overcoverage
-- name    : ConformalBeyondExchangeability.nonexchangeable_conformal_overcoverage
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T07:51:00.731253+00:00
-- url     : https://prove2.me/theorems/7d2247ab-2632-4ea7-a220-86e636aec428
-- title:
--   Theorem 3: upper bound on the coverage of nonexchangeable conformal prediction
-- statement:
--   Let the data $Z$ have an arbitrary joint law $P$, let $w_1,\dots,w_n\in[0,1]$ with normalized weights $\tilde w_i$, and let $\alpha\in(0,1)$.
--
--   1. **Full conformal.** Let $\mathcal A$ be a tagged algorithm with fixed tags whose residual map $z\mapsto R(z)$ is measurable. If $R^{Y_{n+1},K}_1,\dots,R^{Y_{n+1},K}_{n+1}$ are distinct with probability $1$, then the nonexchangeable full conformal set (eq. (18)) satisfies
--   $$P\{Y_{n+1}\in\hat C_n(X_{n+1})\}<1-\alpha+\tilde w_{n+1}+\sum_{i=1}^n\tilde w_i\cdot\mathsf d_{\mathsf{TV}}\big(R(Z),R(Z^i)\big).$$
--   2. **Split conformal.** For a measurable pre-fitted $\hat\mu$ whose residuals $|Y_i-\hat\mu(X_i)|$, $i=1,\dots,n+1$, are distinct with probability $1$, the interval of eq. (11) satisfies the same bound with $R(Z)_i=|Y_i-\hat\mu(X_i)|$.
--
--   Together with Theorem 2, this shows that mild violations of exchangeability cause only mild over-coverage when $\tilde w_{n+1}$ is small.
--
--   **Formalization Note** "Distinct with probability 1" in the full conformal case refers to the pair $(Z,K)$. It is written as $\sum_k\tilde w_k\,P\{R^{Y_{n+1},k}\text{ has distinct entries}\}=1$.
-- source:
--   Barber, Candès, Ramdas and Tibshirani, Conformal prediction beyond exchangeability, arXiv:2202.13415v5 (2023), Section 4.2, Theorem 3, p. 16; proof in Appendix E.2, pp. 44-45

import Mathlib
import Definitions.Def_ConformalBeyondExchangeability_Basic

open MeasureTheory

namespace ConformalBeyondExchangeability

theorem nonexchangeable_conformal_overcoverage {X T : Type*} [MeasurableSpace X] {n : ℕ}
    (P : Measure (Fin (n + 1) → X × ℝ)) [IsProbabilityMeasure P]
    (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    (∀ (alg : TaggedAlg X T) (t : Fin (n + 1) → T), Measurable (residuals alg t) →
      randIndexProb P w
          (fun k => {z | Function.Injective (swapResiduals alg t z (z (Fin.last n)).2 k)}) = 1 →
      fullCoverage P alg t w α <
        1 - α + normWeights w (Fin.last n) + swapGap P w (residuals alg t)) ∧
    (∀ μ : X → ℝ, Measurable μ → (∀ᵐ z ∂P, Function.Injective (splitResiduals μ z)) →
      splitCoverage P μ w α <
        1 - α + normWeights w (Fin.last n) + swapGap P w (splitResiduals μ)) := by sorry

end ConformalBeyondExchangeability
