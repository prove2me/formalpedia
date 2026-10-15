-- Prove2me | Theorems.Thm_FixedPointAA_Main_amplitude_chebyshev
-- name    : FixedPointAA.Main.amplitude_chebyshev
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T23:02:11.115984+00:00
-- url     : https://prove2.me/theorems/578b7fb4-c264-41db-8195-733efca5ef83
-- title:
--   p. 3 after Eq. (15) — final amplitude as a Chebyshev quotient
-- statement:
--   Let $0<\lambda\le1$, $0<\delta\le1$, $L=2l+1$, $x=\cos(\phi/2)$ with $\phi=2\arcsin\sqrt\lambda$, and $\gamma^{-1}=T_{1/L}(1/\delta)$. For the phases $\zeta_h$ of Eq. (13), the upper coordinate after $L$ equatorial rotations is
--
--   $$a_L^{(\gamma)}(x)=\frac{T_L(x/\gamma)}{T_L(1/\gamma)}.$$
--
--   This identifies the failure amplitude required to obtain Eq. (1).
-- source:
--   Yoder, Low, Chuang, Fixed-point quantum search with an optimal number of queries, arXiv:1409.3305v2, p. 3, after Eq. (15)

import Mathlib
import Definitions.Def_FixedPointAA_Main_Setting

namespace FixedPointAA.Main

/-- The Chebyshev form of the last upper amplitude, after Eq. (15). -/
theorem amplitude_chebyshev (lam δ : ℝ) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (l : ℕ) :
    amp (blochAngle lam) (zeta l δ) (2 * l + 1) =
      ((chebT (2 * l + 1)
        (Real.cos (blochAngle lam / 2) * gammaInv (2 * l + 1) δ) /
        chebT (2 * l + 1) (gammaInv (2 * l + 1) δ) : ℝ) : ℂ) := by sorry

end FixedPointAA.Main
