-- Prove2me | Theorems.Thm_FixedPointAA_Main_amplitude_recurrence
-- name    : FixedPointAA.Main.amplitude_recurrence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T23:02:27.029041+00:00
-- url     : https://prove2.me/theorems/080a48b1-86ae-4f8f-b693-358e3fdfe3db
-- title:
--   Eq. (15), p. 3 — recurrence of the upper amplitude
-- statement:
--   For an arbitrary real phase sequence $\zeta_h$ and equatorial rotation angle $\phi$, let $a_h$ be the upper coordinate of $A_{\zeta_h}\cdots A_{\zeta_1}|\bar t\rangle$ and $x=\cos(\phi/2)$. Then
--
--   $$a_0=1,\qquad a_1=x,\qquad a_h=x(1+e^{-i(\zeta_h-\zeta_{h-1})})a_{h-1}-e^{-i(\zeta_h-\zeta_{h-1})}a_{h-2}\quad(h\ge2).$$
--
--   The recurrence is the algebraic bridge between the rotation product and its Chebyshev amplitude. It holds for any real phase sequence, beyond the particular phases chosen in Eq. (13).
-- source:
--   Yoder, Low, Chuang, Fixed-point quantum search with an optimal number of queries, arXiv:1409.3305v2, p. 3, Eqs. (14)–(15)

import Mathlib
import Definitions.Def_FixedPointAA_Main_Setting

namespace FixedPointAA.Main

/-- Eq. (15), which in fact holds for every sequence of equatorial phases. -/
theorem amplitude_recurrence (φ : ℝ) (ζ : ℕ → ℝ) :
    amp φ ζ 0 = 1 ∧ amp φ ζ 1 = (Real.cos (φ / 2) : ℂ) ∧
    ∀ h : ℕ, 2 ≤ h →
      amp φ ζ h =
        (Real.cos (φ / 2) : ℂ) *
          (1 + Complex.exp (-(((ζ h - ζ (h - 1) : ℝ) : ℂ) * Complex.I))) * amp φ ζ (h - 1) -
        Complex.exp (-(((ζ h - ζ (h - 1) : ℝ) : ℂ) * Complex.I)) * amp φ ζ (h - 2) := by sorry

end FixedPointAA.Main
