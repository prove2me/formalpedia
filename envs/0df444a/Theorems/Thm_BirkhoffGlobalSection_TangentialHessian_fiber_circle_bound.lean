-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_fiber_circle_bound
-- name    : BirkhoffGlobalSection.TangentialHessian.fiber_circle_bound
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-29T17:30:49.086396+00:00
-- url     : https://prove2.me/theorems/30a88ece-1e4f-4bd2-9544-7d007389cc76
-- title:
--   Positivity on the fiber circle from harmonic-amplitude bounds
-- statement:
--   Let $x, y, \rho, Z, u, w, \zeta, c_0, \beta_1, \beta_2, P, q, R$ be real numbers (and $c$ an unused parameter) with:
--   - $R = \rho$, $\rho \ge 0$, $x^2 + y^2 = \rho$, $Z \ge 0$;
--   - $Z^2 = u^2 + 4w^2$ and $u + Z = 2\zeta$;
--   - $c_0 - 64\zeta R^2 = 4P$ and $\beta_1^2 + \beta_2^2 = 256\,Z q^2$;
--   - $P > 0$ and $16 Z q^2 R < P^2$.
--
--   Then
--   $$0 < (c_0 - 32u\rho^2) + \beta_1 x + \beta_2 y + (-32u\rho)(x^2 - y^2) + 2(-64w\rho)\,xy .$$
--
--   This is the fiber-circle step in the proof that the tangential-Hessian determinant of the rotating Kepler problem is positive, stated with every polynomial piece abstract so that no large expansion is needed. On the fiber circle $x^2 + y^2 = \rho$ the right-hand side is a degree-two trigonometric polynomial:
--   - its second-harmonic amplitude is $32Z\rho^2$ (from $Z^2 = u^2 + 4w^2$);
--   - its constant term minus that amplitude is $4P$;
--   - its first-harmonic amplitude is $\sqrt{\rho}\,|\beta| = 16\sqrt{Z\rho}\,|q|$.
--
--   The hypotheses make the constant term dominate both harmonics, by the square-root-free positivity criterion for degree-two trigonometric polynomials on a circle. In the application, $\zeta = z_1^2$, $w = z_1 z_2$, $u = z_1^2 - z_2^2$ and $Z = |z|^2$.
-- source:
--   Elementary; the fiber-elimination step of Grisa, Exact fiber elimination for the Levi–Civita convexity gates of the planar restricted three-body problem, Zenodo 21270420 (2026), Lemma 3.4 / Theorem 3.7.

import Mathlib.Data.Real.Sqrt

namespace BirkhoffGlobalSection.TangentialHessian

/-- The degree-2 trigonometric bound on the fiber circle, with all polynomial pieces abstract. -/
theorem fiber_circle_bound (x y ρ Z u w z1sq c0 b1 b2 P q R2 c : ℝ)
    (hρ : R2 = ρ) (hρ0 : 0 ≤ ρ) (hxy : x ^ 2 + y ^ 2 = ρ) (hZ : 0 ≤ Z)
    (hZuw : Z ^ 2 = u ^ 2 + 4 * w ^ 2) (hu : u + Z = 2 * z1sq)
    (hc0P : c0 - 64 * z1sq * R2 ^ 2 = 4 * P) (hb : b1 ^ 2 + b2 ^ 2 = 256 * Z * q ^ 2)
    (hP : 0 < P) (hW : 16 * Z * q ^ 2 * R2 < P ^ 2) :
    0 < (c0 - 32 * u * ρ ^ 2) + b1 * x + b2 * y + (-32 * u * ρ) * (x ^ 2 - y ^ 2)
      + 2 * (-64 * w * ρ) * x * y := by sorry

end BirkhoffGlobalSection.TangentialHessian
