-- Prove2me | Theorems.Thm_AlgebraicCurve_genus_ratFunc_eq_zero_of_perfectField
-- name    : AlgebraicCurve.genus_ratFunc_eq_zero_of_perfectField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/81dbd743-79d9-5686-a5e2-658a74a13ffa
-- title:
--   The rational function field has genus zero over a perfect field
-- statement:
--   Let $K$ be a perfect field and let $F = \mathrm{RatFunc}\,K$ be its field of rational functions in one variable, viewed as a $K$-algebra. Assume the pair is a curve in the sense of [`AlgebraicCurve.IsCurveOver`](def/AlgebraicCurve_IsCurveOver.html#L15): every nonzero $f \in F$ has a divisor, i.e. a finitely supported $\mathbb{Z}$-valued function on the set of places of $F/K$ (valuation subrings of $F$ containing the image of $K$, different from $F$ itself and principal ideal rings) whose value at each place $v$ is $v.\mathrm{ord}\,f$ and whose degree, the sum of its values weighted by the residue degrees, is $0$; each place has residue field finite-dimensional over $K$; and the module of Kähler differentials $\Omega_{F/K}$ is free of rank one over $F$. Assume further [`AlgebraicCurve.HasCanonicalDivisor`](def/AlgebraicCurve_CanonicalDivisor.html#L14): every nonzero $\omega \in \Omega_{F/K}$ admits a divisor whose value at each place $v$ is $v.\mathrm{ordDifferential}\,\omega = v.\mathrm{ord}(v.\mathrm{differentialCoeff}\,\omega)$. The conclusion is that $\mathrm{genus}\,K\,F = 0$, where the genus is defined, when a nonzero differential $\omega$ exists, as the natural-number quotient by $2$ of the truncation to $\mathbb{N}$ of $\deg(K_\omega) + 2$ for a canonical divisor $K_\omega$ attached to $\omega$, and as $0$ otherwise.
--
--   This is the statement that the projective line over a perfect field $K$, in the guise of the function field $K(X)/K$ with the Kähler-differential definition of the canonical class, has genus zero; it rests on the computation that a canonical divisor of $K(X)/K$ has degree $-2$. It is used for the characteristic-zero and algebraically-closed variants [`AlgebraicCurve.genus_ratFunc_eq_zero`](thm.html#AlgebraicCurve.genus_ratFunc_eq_zero) and [`AlgebraicCurve.genusFF_ratFunc_eq_zero_of_isAlgClosed`](thm.html#AlgebraicCurve.genusFF_ratFunc_eq_zero_of_isAlgClosed) in the development of curves and their divisor class groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_genus_ratFunc_eq_zero_of_perfectField.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.genus_ratFunc_eq_zero_of_perfectField (K : Type*) [Field K] [PerfectField K]
    [AlgebraicCurve.IsCurveOver K (RatFunc K)] [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := RatFunc K)] :
    AlgebraicCurve.genus K (RatFunc K) = 0 := by sorry
