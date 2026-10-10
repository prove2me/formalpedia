-- Prove2me | Theorems.Thm_DSGE_quadratic_roots_outside_unit_disk_iff
-- name    : DSGE.quadratic_roots_outside_unit_disk_iff
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:30:28.062044+00:00
-- url     : https://prove2.me/theorems/1042b233-30fd-4141-9e39-a2a34a9517ee
-- title:
--   Both roots of $z^2 - Tz + D$ lie outside the unit circle iff $D>1$ and $|T|<1+D$
-- statement:
--   Let $T, D$ be real numbers with $D > 0$. Then every complex root $z$ of $z^2 - T z + D$ satisfies $|z| > 1$ if and only if
--   $$
--   D > 1 \quad\text{and}\quad |T| < 1 + D .
--   $$
--
--   This is the two-dimensional Schur–Cohn (Jury) stability test, applied in the outward direction. Applied to the trace $T$ and determinant $D$ of the transition matrix $M$ of the forward form, it turns "both eigenvalues of $M$ are explosive" into explicit parameter inequalities.
--
--   **Formalization Note.** The hypothesis $D > 0$ is needed: e.g. $T = 0$, $D = -4$ has roots $\pm 2$ outside the unit circle while $D > 1$ fails. In the application, $D = \det M > 0$.
-- source:
--   Standard Schur–Cohn / Jury criterion for real quadratics, as used in the determinacy analysis of J. Galí, Monetary Policy, Inflation, and the Business Cycle, Princeton University Press, 2008, Chapter 3 (the basic New Keynesian model under an interest-rate rule); J. Bullard and K. Mitra, Learning about monetary policy rules, J. Monetary Economics 49 (2002) 1105-1129

import Mathlib

namespace DSGE
theorem quadratic_roots_outside_unit_disk_iff (T D : ℝ) (hD : 0 < D) :
    (∀ z : ℂ, z ^ 2 - (T : ℂ) * z + (D : ℂ) = 0 → 1 < ‖z‖) ↔ 1 < D ∧ |T| < 1 + D := by sorry
end DSGE
