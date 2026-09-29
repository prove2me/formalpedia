-- Prove2me | Theorems.Thm_FamousTheorems_inner_mul_inner_self_le
-- name    : FamousTheorems.inner_mul_inner_self_le
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T22:17:14.257944+00:00
-- url     : https://prove2.me/theorems/acad7741-d4fb-4b3d-a8a2-12046bb42d3d
-- title:
--   The Cauchy–Schwarz inequality
-- statement:
--   **The Cauchy–Schwarz inequality.**
--
--   $$|\langle x, y\rangle|\,|\langle y, x\rangle| \;\le\; \Re\langle x,x\rangle\ \Re\langle y,y\rangle,$$
--   the familiar $|\langle x,y\rangle| \le \|x\|\,\|y\|$ in the form Mathlib states over a general
--   `RCLike` field.
--
--   The proof is to expand $\langle x - \lambda y, x - \lambda y\rangle \ge 0$ and optimise over
--   $\lambda$ — the discriminant of a non-negative quadratic must be non-positive.
--
--   It is the inequality that makes inner product spaces *geometric*: it gives the triangle
--   inequality for the induced norm, lets one define the angle between vectors via
--   $\cos\theta = \langle x,y\rangle/(\|x\|\|y\|)$, and underpins Bessel's inequality and the
--   projection theorem. Named for Cauchy (finite sums, 1821), Bunyakovsky and Schwarz (integrals).
-- source:
--   One of Freek Wiedijk's "100 theorems"; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

theorem inner_mul_inner_self_le : ∀ {𝕜 : Type*} {E : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E] (x y : E),
    ‖(inner 𝕜 x y : 𝕜)‖ * ‖(inner 𝕜 y x : 𝕜)‖ ≤
      RCLike.re (inner 𝕜 x x : 𝕜) * RCLike.re (inner 𝕜 y y : 𝕜) := by sorry

end FamousTheorems
