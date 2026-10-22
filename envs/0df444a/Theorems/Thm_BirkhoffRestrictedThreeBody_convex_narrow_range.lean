-- Prove2me | Theorems.Thm_BirkhoffRestrictedThreeBody_convex_narrow_range
-- name    : BirkhoffRestrictedThreeBody.convex_narrow_range
-- status  : Open
-- author  : @Yivy Yu
-- created : 2026-09-10T02:27:41.620777+00:00
-- url     : https://prove2.me/theorems/1a7ae5b0-ae26-46dd-9b0a-97219e6dfdc3
-- title:
--   Proposition 4.4 — narrow-range convexity
-- statement:
--   Let
--
--   $$
--   0\le\mu\le\frac12,
--   \qquad
--   2.1\le c\le2.1+10^{-6}.
--   $$
--
--   Then the compact component $\Sigma_{\mu,c}$ of the Levi-Civita-regularized energy hypersurface is strictly convex. Concretely, for every $s\in\Sigma_{\mu,c}$ and every nonzero tangent vector $v$ satisfying $dK_{\mu,c}(s)[v]=0$, the tangential second derivative is positive:
--
--   $$
--   d\bigl(x\mapsto dK_{\mu,c}(x)[v]\bigr)(s)[v]>0.
--   $$
--
--   This is the positive-tangential-Hessian conclusion of Proposition 4.4 used to prove Theorem 1.5. It is a known result in the narrow validated parameter interval and supplies the current convexity frontier toward Birkhoff's conjecture.
--
--   **Formalization Note.** The component is selected inside $K_{\mu,c}^{-1}(0)\cap\{D>0\}$ by the base point $(0,0,\sqrt{1-\mu},0)$; every parameter endpoint is included.
-- source:
--   Joung--van Koert, Computational symplectic topology and symmetric orbits in the restricted three-body problem, https://arxiv.org/abs/2407.19159, p. 20, Proposition 4.4 and proof of Theorem 1.5; statement on p. 3, Theorem 1.5.

import Definitions.Def_BirkhoffRestrictedThreeBody

namespace BirkhoffRestrictedThreeBody

/-- Joung--van Koert, Theorem 1.5, expressed as positivity of the tangential Hessian. -/
theorem convex_narrow_range (μ c : ℝ) (hμ0 : 0 ≤ μ) (hμhalf : μ ≤ 1 / 2)
    (hc0 : 21 / 10 ≤ c) (hc1 : c ≤ 21 / 10 + 1 / 1000000) :
    IsStrictlyConvexLevel (leviCivitaHamiltonian μ c) (leftEnergyComponent μ c) := by sorry

end BirkhoffRestrictedThreeBody
