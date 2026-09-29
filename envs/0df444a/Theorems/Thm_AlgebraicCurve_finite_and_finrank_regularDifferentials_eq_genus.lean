-- Prove2me | Theorems.Thm_AlgebraicCurve_finite_and_finrank_regularDifferentials_eq_genus
-- name    : AlgebraicCurve.finite_and_finrank_regularDifferentials_eq_genus
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/36752414-1ec4-5b94-8fec-c5a406af6025
-- title:
--   Regular differentials form a space of dimension the genus
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, $K$ algebraically closed, and $F$ essentially of finite type over $K$. Assume [`AlgebraicCurve.IsCurveOver K F`](def/AlgebraicCurve_IsCurveOver.html#L15): every nonzero $f \in F$ has a finitely supported divisor recording its orders $v.\mathrm{ord}\,f$ at all places and of degree $0$; for each place $v$ the residue field of $v$ is a finite $K$-module; and $\Omega_{F/K}$ is free of rank one over $F$. Here a place is a valuation subring of $F$ containing the image of $K$, different from $F$, whose ring is a principal ideal ring. Assume also [`AlgebraicCurve.HasCanonicalDivisor`](def/AlgebraicCurve_CanonicalDivisor.html#L14): every nonzero $\omega \in \Omega_{F/K}$ admits a finitely supported divisor $D$ with $D(v) = v.\mathrm{ordDifferential}\,\omega$ for all $v$. Then the $K$-submodule [`AlgebraicCurve.regularDifferentials K F`](def/AlgebraicCurve_RegularDifferentials.html#L26) of $\Omega_{F/K}$, consisting of those $\omega$ such that for every place $v$ one may write $\omega = f \cdot \mathrm{d}t_v$ with $f$ in the valuation subring of $v$ and $t_v$ a uniformiser at $v$, is a finite-dimensional $K$-vector space, and its $K$-dimension equals [`AlgebraicCurve.genus K F`](def/AlgebraicCurve_CanonicalDivisor.html#L33), namely $(\deg D_\omega + 2)/2$ computed from a canonical divisor of some nonzero differential (and $0$ if $\Omega_{F/K} = 0$).
--
--   This is the identification $\dim_K H^0(X,\Omega^1_X) = g$ for a curve over an algebraically closed field, equivalently $\ell(W) = g$ for a canonical divisor $W$ in the language of function fields; it reconciles the divisor-theoretic definition of the genus used in this development with the dimension of the space of everywhere-regular differentials. It is invoked in the study of $\mathrm{Pic}^0$ and of regular differentials under constant field extension.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_finite_and_finrank_regularDifferentials_eq_genus.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_RegularDifferentials

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.finite_and_finrank_regularDifferentials_eq_genus {K F : Type*} [Field K]
    [Field F] [Algebra K F] [IsAlgClosed K] [Algebra.EssFiniteType K F]
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)] :
    Module.Finite K ↥(AlgebraicCurve.regularDifferentials K F) ∧
      Module.finrank K ↥(AlgebraicCurve.regularDifferentials K F) =
        AlgebraicCurve.genus K F := by sorry
