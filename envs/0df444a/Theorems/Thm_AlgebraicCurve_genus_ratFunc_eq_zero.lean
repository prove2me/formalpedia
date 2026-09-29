-- Prove2me | Theorems.Thm_AlgebraicCurve_genus_ratFunc_eq_zero
-- name    : AlgebraicCurve.genus_ratFunc_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/36414540-90fd-5133-9d78-0fac6d18a881
-- title:
--   Genus of K(X) is zero in characteristic zero
-- statement:
--   Let $K$ be a field of characteristic zero and let $F = \mathrm{RatFunc}\,K$ be the field of rational functions in one variable over $K$, viewed as a $K$-algebra. Two hypotheses on this extension are assumed. First, [`AlgebraicCurve.IsCurveOver K (RatFunc K)`](def/AlgebraicCurve_IsCurveOver.html#L15): every nonzero $f \in F$ has an associated divisor, i.e. a finitely supported function $D$ from places of $F/K$ to $\mathbb{Z}$ with $D(v) = v.\mathrm{ord}(f)$ at every place $v$ and with $\deg D = \sum_v D(v)\cdot\deg v = 0$; the residue field of each place is a finite-dimensional $K$-module; and $\Omega_{F/K}$ is a free $F$-module of rank one. Here a place of $F/K$ is a valuation subring of $F$ containing $\mathrm{im}(K \to F)$, not equal to all of $F$, and a principal ideal ring. Second, [`AlgebraicCurve.HasCanonicalDivisor`](def/AlgebraicCurve_CanonicalDivisor.html#L14): every nonzero $\omega \in \Omega_{F/K}$ admits a divisor $D$ with $D(v) = v.\mathrm{ord}(v.\mathrm{differentialCoeff}\,\omega)$ for all $v$. Under these hypotheses the conclusion is that [`AlgebraicCurve.genus K (RatFunc K)`](def/AlgebraicCurve_CanonicalDivisor.html#L33) is $0$; by definition this genus is $\lfloor (\deg D_\omega + 2)^{+}/2 \rfloor$ for a canonical divisor $D_\omega$ attached to some chosen nonzero differential $\omega$, and $0$ if $\Omega_{F/K}$ is zero.
--
--   This is the statement that the projective line over a field of characteristic zero has genus zero, in the form used by this development's divisor-theoretic framework for curves. It feeds into [`AlgebraicCurve.finsum_ramificationIndexAlong_sub_one_eq`](thm.html#AlgebraicCurve.finsum_ramificationIndexAlong_sub_one_eq), where the genus of the rational function field enters the ramification count for a map to the line.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_genus_ratFunc_eq_zero.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.genus_ratFunc_eq_zero (K : Type*) [Field K] [CharZero K]
    [AlgebraicCurve.IsCurveOver K (RatFunc K)] [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := RatFunc K)] :
    AlgebraicCurve.genus K (RatFunc K) = 0 := by sorry
