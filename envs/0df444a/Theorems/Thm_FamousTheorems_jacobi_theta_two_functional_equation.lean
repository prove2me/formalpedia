-- Prove2me | Theorems.Thm_FamousTheorems_jacobi_theta_two_functional_equation
-- name    : FamousTheorems.jacobi_theta_two_functional_equation
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:38:42.711911+00:00
-- url     : https://prove2.me/theorems/46eaa2f7-7376-4f99-a2b1-d729c9bb2aba
-- title:
--   The functional equation of the two-variable Jacobi theta function
-- statement:
--   **The functional equation of the two-variable Jacobi theta function.** Let $\theta(z,\tau)=\sum_{n\in\mathbb Z}e^{2\pi inz+\pi in^2\tau}$. For all $z,\tau\in\mathbb C$,
--   $$\theta(z,\tau)=\frac{1}{(-i\tau)^{1/2}}\,e^{-\pi iz^2/\tau}\,\theta\Big(\frac z\tau,-\frac1\tau\Big).$$
--
--   This is Jacobi's imaginary transformation, the two-variable form of the modularity of $\theta$. It is a consequence of Poisson summation. It is basic to the theory of theta functions, Jacobi forms and elliptic functions, and it gives the functional equations of Hurwitz zeta functions and Dirichlet $L$-functions.
--
--   **Formalization note.** Mathlib's `jacobiTheta₂_functional_equation`. `jacobiTheta₂ z τ` is the series above, and the power is the complex power `cpow`. The identity holds for all $z,\tau\in\mathbb C$. Where $\operatorname{Im}\tau\le0$ the series does not converge, so Mathlib's `tsum` gives the value $0$, and the identity still holds with that convention.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `jacobiTheta₂_functional_equation`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem jacobi_theta_two_functional_equation (z τ : ℂ) :
    jacobiTheta₂ z τ = 1 / (-Complex.I * τ) ^ (1 / 2 : ℂ) * Complex.exp (-(Real.pi : ℂ) * Complex.I * z ^ 2 / τ) *
      jacobiTheta₂ (z / τ) (-1 / τ) := by sorry

end FamousTheorems
