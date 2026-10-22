-- Prove2me | Theorems.Thm_FixedPointAA_Main_reflections_as_rotations
-- name    : FixedPointAA.Main.reflections_as_rotations
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T23:02:03.778273+00:00
-- url     : https://prove2.me/theorems/858f75c6-9c19-40e6-9c15-c6544197b4d4
-- title:
--   Eqs. (8)–(9), p. 2 — reflections as Bloch rotations
-- statement:
--   For $0\le\lambda\le1$ let $\phi=2\arcsin\sqrt\lambda$. Define $R_\varphi(\theta)=\exp[-i\theta(\cos\varphi Z+\sin\varphi X)/2]$, with Pauli matrices $X,Z$. Then for real $\alpha,\beta$,
--
--   $$S_s(\alpha)=e^{-i\alpha/2}R_\phi(\alpha),\qquad S_t(\beta)=e^{i\beta/2}R_0(\beta).$$
--
--   This expresses the phase reflections as Bloch-sphere rotations and feeds the product rearrangement on p. 3.
-- source:
--   Yoder, Low, Chuang, Fixed-point quantum search with an optimal number of queries, arXiv:1409.3305v2, p. 2, Eqs. (8)–(9)

import Mathlib
import Definitions.Def_FixedPointAA_Main_Setting

namespace FixedPointAA.Main

/-- Eqs. (8)–(9), with `φ` defined by the initial target overlap. -/
theorem reflections_as_rotations (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (α β : ℝ) :
    Ss (sVec lam) α =
      Complex.exp (-((α / 2 : ℝ) : ℂ) * Complex.I) • R (blochAngle lam) α ∧
    St tVec β = Complex.exp (((β / 2 : ℝ) : ℂ) * Complex.I) • R 0 β := by sorry

end FixedPointAA.Main
