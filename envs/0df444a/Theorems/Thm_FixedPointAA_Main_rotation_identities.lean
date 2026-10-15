-- Prove2me | Theorems.Thm_FixedPointAA_Main_rotation_identities
-- name    : FixedPointAA.Main.rotation_identities
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T23:02:14.562726+00:00
-- url     : https://prove2.me/theorems/6c378354-eb1e-4b5d-8a04-e9ba8c40010a
-- title:
--   p. 3 after Eq. (11) — state preparation and rotation identities
-- statement:
--   Let $0\le\lambda\le1$, $\phi=2\arcsin\sqrt\lambda$, and $A_\zeta=\exp[-i\phi(\cos\zeta X+\sin\zeta Y)/2]$. For real $\alpha,\beta$, the state-preparation action and two conjugation identities are
--
--   $$A_{\pi/2}|\bar t\rangle=|s\rangle,\qquad R_\phi(\alpha)=A_{\pi/2}R_0(\alpha)A_{-\pi/2},\qquad A_{\alpha+\beta}=R_0(\beta)A_\alpha R_0(-\beta).$$
--
--   These identities are used to convert the Grover sequence into an ordered equatorial-rotation product.
-- source:
--   Yoder, Low, Chuang, Fixed-point quantum search with an optimal number of queries, arXiv:1409.3305v2, p. 3, after Eq. (11)

import Mathlib
import Definitions.Def_FixedPointAA_Main_Setting

namespace FixedPointAA.Main
open scoped Matrix

/-- State preparation and the two rotation identities following Eq. (11). -/
theorem rotation_identities (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (α β : ℝ) :
    A (blochAngle lam) (Real.pi / 2) *ᵥ tbarVec = sVec lam ∧
    R (blochAngle lam) α =
      A (blochAngle lam) (Real.pi / 2) * R 0 α * A (blochAngle lam) (-Real.pi / 2) ∧
    A (blochAngle lam) (α + β) =
      R 0 β * A (blochAngle lam) α * R 0 (-β) := by sorry

end FixedPointAA.Main
