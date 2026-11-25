-- Prove2me | Theorems.Thm_ConformalBeyondExchangeability_full_conformal_coverage_exchangeable
-- name    : ConformalBeyondExchangeability.full_conformal_coverage_exchangeable
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T07:46:57.697089+00:00
-- url     : https://prove2.me/theorems/db0559b0-9e4d-423b-aebc-9471a12e90c3
-- title:
--   Theorem 1: full and split conformal prediction under exchangeability
-- statement:
--   Let $(X_1,Y_1),\dots,(X_{n+1},Y_{n+1})$ be exchangeable, i.e. their joint law $P$ is invariant under every permutation of the $n+1$ indices. Let $\alpha\in(0,1)$.
--
--   1. **Full conformal.** Let $\mathcal A$ be an algorithm that treats the data points symmetrically (eq. (6)), and suppose the residual vector $z\mapsto(|y_i-\hat\mu(x_i)|)_{i\le n+1}$, $\hat\mu=\mathcal A(z_1,\dots,z_{n+1})$, is measurable. Then the full conformal set of eq. (8),
--   $$\hat C_n(X_{n+1})=\Big\{y:R^y_{n+1}\le\mathsf Q_{1-\alpha}\Big(\sum_{i=1}^{n+1}\tfrac1{n+1}\delta_{R^y_i}\Big)\Big\},$$
--   satisfies $P\{Y_{n+1}\in\hat C_n(X_{n+1})\}\ge1-\alpha$.
--   2. **Split conformal.** For every measurable pre-fitted $\hat\mu:\mathcal X\to\mathbb R$, the split conformal interval of eq. (5), $\hat\mu(X_{n+1})\pm\mathsf Q_{1-\alpha}(\sum_{i=1}^n\frac1{n+1}\delta_{R_i}+\frac1{n+1}\delta_{+\infty})$ with $R_i=|Y_i-\hat\mu(X_i)|$, covers $Y_{n+1}$ with probability at least $1-\alpha$.
--
--   This is the classical guarantee of Vovk et al. that Theorem 2 generalizes.
--
--   **Formalization Note** The sets of eqs. (5) and (8) are the weighted sets of eqs. (11) and (12) with $w_1=\dots=w_n=1$, since then $\tilde w_i=1/(n+1)$. The algorithm is deterministic; the paper's footnote 2 also allows randomized symmetric algorithms, which are not covered. Measurability of the residual map is the standing convention that makes the probabilities defined.
-- source:
--   Barber, Candès, Ramdas and Tibshirani, Conformal prediction beyond exchangeability, arXiv:2202.13415v5 (2023), Section 2, Theorem 1, eqs. (5)-(8), p. 7; proof in Section 6.1, p. 29

import Mathlib
import Definitions.Def_ConformalBeyondExchangeability_Basic

open MeasureTheory

namespace ConformalBeyondExchangeability

theorem full_conformal_coverage_exchangeable {X : Type*} [MeasurableSpace X] {n : ℕ}
    (P : Measure (Fin (n + 1) → X × ℝ)) [IsProbabilityMeasure P] (hP : IsExchangeable P)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    (∀ alg : Alg X, IsSymmetric alg → Measurable (symResiduals (n := n) alg) →
      1 - α ≤ P.real {z | (z (Fin.last n)).2 ∈ symFullSet alg (fun _ => 1) α z}) ∧
    (∀ μ : X → ℝ, Measurable μ → 1 - α ≤ splitCoverage P μ (fun _ => 1) α) := by sorry

end ConformalBeyondExchangeability
