-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_radial_derivative_pos_of_reduced
-- name    : BirkhoffGlobalSection.TangentialHessian.radial_derivative_pos_of_reduced
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-26T17:40:14.681993+00:00
-- url     : https://prove2.me/theorems/24848cc7-29f0-4fc7-8f2e-0a96c3d3a661
-- title:
--   Radial derivative $s\cdot\nabla K$ from two reduced polynomial inequalities
-- statement:
--   Throughout, $\mathrm{Phase}=\mathbb R^4$ with coordinates $s=(z_1,z_2,w_1,w_2)$ of the Levi-Civita regularization $q+\mu=2z^2$, $p=w/\bar z$ of the planar circular restricted three-body problem at the primary of mass $1-\mu$ located at $(-\mu,0)$. The regularized Hamiltonian at the Jacobi level $H=-c$ is $K_{\mu,c}=P-\mu Z/r$, where $Z=z_1^2+z_2^2$, $r=\lvert 2z^2-1\rvert=\sqrt{D}$ with $D=(2(z_1^2-z_2^2)-1)^2+(4z_1z_2)^2$, and $P$ is the polynomial part of eq. (2.2). The set $U=\{D>0\}$ excludes the (unregularized) second collision.
--
--   Fix $\mu,c\in\mathbb R$, a point $s=(z,w)$ and any $r>0$, and write $Z=\lvert z\rvert^2$ and $u=z_1^2-z_2^2$. Assume $s$ lies on the zero level in the form $P(s)-\mu Z/r=0$. Let
--
--   $$
--   E\,r^3=r^3\big((1-\mu)-8Z^3+4\mu Zu\big)+4\mu Z(2Z^2-u),
--   $$
--   $$
--   R^2r=r\big((1-\mu)-2cZ+(4Z^2+\mu^2)Z-4\mu Zu\big)+2\mu Z,
--   $$
--   $$
--   F\,r^6=(E\,r^3)^2-16Z^3r^5\,(R^2r).
--   $$
--
--   If $E\,r^3>0$ and $F\,r^6>0$, then the radial derivative is positive:
--
--   $$
--   \sum_{i=1}^4 s_i\,\nabla K_{\mu,c}(s)_i\;>\;0 ,
--   $$
--
--   where $\nabla K$ is the explicit gradient with the given $r$. On the energy surface one takes $r=\lvert 2z^2-1\rvert$. Positivity of the radial derivative implies $\nabla K\ne0$ and star-shapedness of the energy surface. The statement eliminates the momentum $w$ entirely: the remaining inequalities involve only $(\mu,c,Z,u,r)$.
-- source:
--   Joung–van Koert, Computational symplectic topology and symmetric orbits in the restricted three-body problem, https://arxiv.org/abs/2407.19159v3, Proposition 4.4 (regularity ∇K ≠ 0 of Σ_{μ,c}); reduction via the form (4.1).

import Definitions.Def_BirkhoffGlobalSection_TangentialHessian

namespace BirkhoffGlobalSection.TangentialHessian

/-- On the zero level `K = 0` (for any `r > 0`; on the energy surface `r = |2z² - 1|`), positivity of the two reduced
polynomials `E r³` and `F r⁶` in `(μ, c, Z, u, r)` implies positivity of the radial derivative
`s · ∇K`. -/
theorem radial_derivative_pos_of_reduced (μ c r : ℝ) (s : Phase)
    (hr : 0 < r)
    (hK : pP μ c s - μ * (zNormSq s / r) = 0)
    (hpoly : 0 < radEr3 μ (zNormSq s) (uCoord s) r ∧
      0 < radFr6 μ c (zNormSq s) (uCoord s) r) :
    0 < ∑ i, s i * kGradR μ c r s i := by sorry

end BirkhoffGlobalSection.TangentialHessian
