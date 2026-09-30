-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_mu_zero_univariate
-- name    : BirkhoffGlobalSection.TangentialHessian.mu_zero_univariate
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-29T17:30:29.632281+00:00
-- url     : https://prove2.me/theorems/8ab28b2c-d158-4d9d-98c3-177a75e78d5b
-- title:
--   Univariate polynomial inequalities for the Kepler case of the tangential Hessian
-- statement:
--   For real numbers $Z, c$ with $0 \le Z \le \tfrac{3}{10}$ and $\tfrac{21}{10} \le c \le \tfrac{21}{10} + 10^{-6}$, put
--   $$P(Z) = 224Z^7 - 224cZ^5 + 148Z^4 + 24c^2Z^3 - 20cZ^2 - 4Z + c^2,\qquad q(Z) = 60Z^5 - 44cZ^3 + 24Z^2 + 3c^2Z - 2c,$$
--   and $R(Z) = 1 - 2cZ + 4Z^3$. Then
--   $$P(Z) > 0 \qquad\text{and}\qquad 16\,Z\,q(Z)^2 R(Z) < P(Z)^2 .$$
--
--   These are the two univariate inequalities to which the tangential-Hessian determinant of the Levi-Civita regularized rotating Kepler problem reduces. They are the case $\mu = 0$ of the positive-tangential-Hessian clause of Joung–van Koert, Proposition 4.4.
--   - $Z = |z|^2$ is the squared Levi-Civita base radius.
--   - $R(Z)$ is the squared fiber radius.
--   - $4P$ is the constant term minus the second-harmonic amplitude of the fiber form.
--   - $16\sqrt{Z}\,|q|$ is its first-harmonic amplitude divided by the fiber radius.
--
--   **Formalization note.** Both inequalities are established over the box $[0, \tfrac{5}{16}] \times [c_-, c_+]$ ($c_\pm$ dyadic, enclosing the $c$-window) by a two-leaf centred-form interval certificate, checked in the kernel with the interval-checker definitions published for this project.
-- source:
--   Kepler (mu = 0) specialisation of the convexity gate behind Joung–van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 4.4; verified by an exact interval certificate.

import Mathlib.Data.Real.Basic

namespace BirkhoffGlobalSection.TangentialHessian

/-- The two univariate inequalities of the rotating Kepler case. -/
theorem mu_zero_univariate (Z c : ℝ) (hZ0 : 0 ≤ Z) (hZ : Z ≤ 3 / 10)
    (hc0 : 21 / 10 ≤ c) (hc1 : c ≤ 21 / 10 + 1 / 1000000) :
    0 < (224 * Z ^ 7 - 224 * c * Z ^ 5 + 148 * Z ^ 4 + 24 * c ^ 2 * Z ^ 3 - 20 * c * Z ^ 2 - 4 * Z + c ^ 2) ∧ 16 * Z * (60 * Z ^ 5 - 44 * c * Z ^ 3 + 24 * Z ^ 2 + 3 * c ^ 2 * Z - 2 * c) ^ 2 * (1 - 2 * c * Z + 4 * Z ^ 3) < (224 * Z ^ 7 - 224 * c * Z ^ 5 + 148 * Z ^ 4 + 24 * c ^ 2 * Z ^ 3 - 20 * c * Z ^ 2 - 4 * Z + c ^ 2) ^ 2 := by sorry

end BirkhoffGlobalSection.TangentialHessian
