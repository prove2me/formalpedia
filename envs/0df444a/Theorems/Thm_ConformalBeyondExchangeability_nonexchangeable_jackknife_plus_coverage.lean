-- Prove2me | Theorems.Thm_ConformalBeyondExchangeability_nonexchangeable_jackknife_plus_coverage
-- name    : ConformalBeyondExchangeability.nonexchangeable_jackknife_plus_coverage
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T07:52:00.493447+00:00
-- url     : https://prove2.me/theorems/27f66f19-6229-4a2c-a04e-2aad4039ca0d
-- title:
--   Theorem 5: nonexchangeable jackknife+
-- statement:
--   Let the data $Z$ have an arbitrary joint law $P$. Let $w_1,\dots,w_n\in[0,1]$ with normalized weights $\tilde w_i$, let $\alpha\in(0,1)$, and let $\mathcal A$ be a tagged algorithm with fixed tags $t_1,\dots,t_{n+1}$. Suppose the map $z\mapsto R_{\mathrm{jack+}}(z)$ to the matrix of leave-two-out residuals is measurable. Then the nonexchangeable jackknife+ interval (eq. (34)), built with the random index $K$ drawn independently of $Z$, satisfies
--   $$P\{Y_{n+1}\in\hat C_n(X_{n+1})\}\ge1-2\alpha-\sum_{i=1}^n\tilde w_i\cdot\mathsf d_{\mathsf{TV}}\big(R_{\mathrm{jack+}}(Z),R_{\mathrm{jack+}}(Z^i)\big).$$
--
--   **Formalization Note** The left endpoint uses the largest $\alpha$-quantile and the right endpoint the smallest $(1-\alpha)$-quantile, as in footnote 7. The probability over $(Z,K)$ is the sum $\sum_k\tilde w_k\,P\{\cdot\}$.
-- source:
--   Barber, Candès, Ramdas and Tibshirani, Conformal prediction beyond exchangeability, arXiv:2202.13415v5 (2023), Appendix B.3, Theorem 5, eq. (34), p. 40; proof in Appendix E.4.2, pp. 50-51

import Mathlib
import Definitions.Def_ConformalBeyondExchangeability_Basic

open MeasureTheory

namespace ConformalBeyondExchangeability

theorem nonexchangeable_jackknife_plus_coverage {X T : Type*} [MeasurableSpace X] {n : ℕ}
    (P : Measure (Fin (n + 1) → X × ℝ)) [IsProbabilityMeasure P]
    (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (alg : TaggedAlg X T) (t : Fin (n + 1) → T) (hR : Measurable (jackResiduals alg t)) :
    1 - 2 * α - swapGap P w (jackResiduals alg t) ≤ jackCoverage P alg t w α := by sorry

end ConformalBeyondExchangeability
