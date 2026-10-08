-- Prove2me | Theorems.Thm_BoydADMM_Consensus_l1_prox_soft_threshold
-- name    : BoydADMM.Consensus.l1_prox_soft_threshold
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:06:33.524218+00:00
-- url     : https://prove2.me/theorems/c88bab08-0379-4022-a9b1-d718188b553e
-- title:
--   §7.1.1: for $g=\lambda\|\cdot\|_1$ the proximal step is soft thresholding $S_{\lambda/N\rho}$
-- statement:
--   Let $N\ge1$, $\rho>0$, $\lambda>0$ and $g(z)=\lambda\|z\|_1$. With $v=\bar x^{k+1}+(1/\rho)\bar y^k$, the proximal step of the regularized consensus $z$-update,
--   $$\operatorname*{minimize}_{z\in\mathbb R^n}\ \lambda\|z\|_1+(N\rho/2)\,\|z-v\|_2^2,$$
--   has the unique solution
--   $$z_j=S_{\lambda/N\rho}(v_j),\qquad j=1,\dots,n,$$
--   where $S_\kappa$ is soft thresholding.
--
--   **Formalization Note** The book prints $z^{k+1}:=S_{\lambda/N\rho}(\bar x^{k+1}-(1/\rho)\bar y^k)$; the intended reading, forced by the proximal form of the $z$-update displayed just above it on the same page, is $\bar x^{k+1}+(1/\rho)\bar y^k$, which is what is stated. $\lambda$ is named `lam` in Lean. The statement is an "iff" (existence and uniqueness of the minimizer).
-- source:
--   Boyd, Parikh, Chu, Peleato, Eckstein, Distributed Optimization and Statistical Learning via the Alternating Direction Method of Multipliers, Found. Trends Mach. Learn. 3(1) (2011), p. 52, §7.1.1 (example g(z) = λ‖z‖₁; the book prints x̄^{k+1} − (1/ρ)ȳ^k, corrected to +)

import Mathlib
import Definitions.Def_BoydADMM_Consensus_Model

open scoped BigOperators InnerProductSpace

namespace BoydADMM.Consensus

/-- §7.1.1, p. 52 (sign corrected): for `g(z) = λ‖z‖₁` with `λ > 0` (`lam` in Lean), the
proximal step `argmin_z (λ‖z‖₁ + (Nρ/2)‖z − x̄^{k+1} − (1/ρ)ȳ^k‖²)` has the unique solution
`z = S_{λ/Nρ}(x̄^{k+1} + (1/ρ)ȳ^k)`, componentwise. The book prints `x̄^{k+1} − (1/ρ)ȳ^k`. -/
theorem l1_prox_soft_threshold {n N : ℕ} (hN : 0 < N) (ρ : ℝ) (hρ : 0 < ρ)
    (lam : ℝ) (hlam : 0 < lam)
    (x y : Fin N → EuclideanSpace ℝ (Fin n)) (z : EuclideanSpace ℝ (Fin n)) :
    (∀ z' : EuclideanSpace ℝ (Fin n),
        lam * ∑ j, |z j| + ((N : ℝ) * ρ / 2) * ‖z - avg x - (1 / ρ) • avg y‖ ^ 2 ≤
          lam * ∑ j, |z' j| + ((N : ℝ) * ρ / 2) * ‖z' - avg x - (1 / ρ) • avg y‖ ^ 2) ↔
      ∀ j, z j = BoydADMM.Prox.softThreshold (lam / ((N : ℝ) * ρ)) ((avg x + (1 / ρ) • avg y) j) := by sorry

end BoydADMM.Consensus
