-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_radial_poly_pos
-- name    : BirkhoffGlobalSection.TangentialHessian.radial_poly_pos
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-26T18:08:01.690962+00:00
-- url     : https://prove2.me/theorems/6b454a5f-744a-4e09-8104-a29031503676
-- title:
--   Reduced radial-derivative inequalities $E\,r^3>0$ and $F\,r^6>0$
-- statement:
--   Let $0\le\mu\le\tfrac12$ and $\tfrac{21}{10}\le c\le\tfrac{21}{10}+10^{-6}$. Let $Z,u,r$ be real numbers with
--
--   $$
--   0\le Z,\qquad 2Z\le\frac{3-2\mu}{5},\qquad \lvert u\rvert\le Z,\qquad r>0,\qquad r^2=4Z^2-4u+1,
--   $$
--
--   and with $R^2r\ge0$, where
--
--   $$
--   R^2r=r\big((1-\mu)-2cZ+(4Z^2+\mu^2)Z-4\mu Zu\big)+2\mu Z .
--   $$
--
--   Then
--
--   $$
--   E\,r^3=r^3\big((1-\mu)-8Z^3+4\mu Zu\big)+4\mu Z(2Z^2-u)\;>\;0
--   $$
--
--   and
--
--   $$
--   F\,r^6=(E\,r^3)^2-16Z^3r^5\,(R^2r)\;>\;0 .
--   $$
--
--   Here $Z=\lvert z\rvert^2$, $u=z_1^2-z_2^2$ and $r=\lvert 2z^2-1\rvert$ are the reduced variables of the Levi-Civita energy surface, and $R^2$ is the squared radius of its momentum fiber. By [radial_derivative_pos_of_reduced](p2m:theorem/24848cc7-29f0-4fc7-8f2e-0a96c3d3a661), these two inequalities imply that the radial derivative $s\cdot\nabla K_{\mu,c}$ is positive on the left energy component. This is the regularity part (C) of Proposition 4.4.
--
--   Status note: a computer-assisted proof exists as an exact interval subdivision certificate (1599 boxes, centred-form enclosures) checked by the Lean kernel without `native_decide`. It needs about 24 minutes of kernel time, which exceeds the platform's compile limit, so it is not submitted here.
-- source:
--   Joung–van Koert, Computational symplectic topology and symmetric orbits in the restricted three-body problem, https://arxiv.org/abs/2407.19159v3, Proposition 4.4 (regularity of Σ_{μ,c}; the box computation), reduced via the form (4.1).

import Definitions.Def_BirkhoffGlobalSection_TangentialHessian

namespace BirkhoffGlobalSection.TangentialHessian

/-- The two reduced polynomial inequalities behind positivity of the radial derivative
on the left energy component: `E r³ > 0` and `F r⁶ > 0` over the reduced variables. -/
theorem radial_poly_pos (μ c Z u r : ℝ)
    (hμ0 : 0 ≤ μ) (hμhalf : μ ≤ 1 / 2)
    (hc0 : 21 / 10 ≤ c) (hc1 : c ≤ 21 / 10 + 1 / 1000000)
    (hZ : 0 ≤ Z) (hz : 2 * Z ≤ (3 - 2 * μ) / 5) (hu1 : u ≤ Z) (hu2 : -Z ≤ u)
    (hr : 0 < r) (hr2 : r ^ 2 = 4 * Z ^ 2 - 4 * u + 1) (hR : 0 ≤ radrR2 μ c Z u r) :
    0 < radEr3 μ Z u r ∧ 0 < radFr6 μ c Z u r := by sorry

end BirkhoffGlobalSection.TangentialHessian
