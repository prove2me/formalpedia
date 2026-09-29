-- Prove2me | Theorems.Thm_AlgebraicCurve_IsCurveOver_trdeg_eq_one
-- name    : AlgebraicCurve.IsCurveOver.trdeg_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/f76e42fa-4d43-55dd-b8ab-bfdb07bdc38b
-- title:
--   A curve over a perfect field has transcendence degree one
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, $K$ perfect, and $F$ essentially of finite type over $K$, and assume $F$ is a curve over $K$ in the sense of the project predicate `IsCurveOver K F`, namely: (i) principal divisors exist, i.e. for every $f \in F$ with $f \neq 0$ there is a divisor $D$ on $K$, $F$ whose value at each place $v$ is $v.\mathrm{ord}(f)$ and whose degree is $0$; (ii) for every place $v$ the residue field of $v$ is a finite-dimensional $K$-module; and (iii) the module of Kähler differentials $\Omega_{F/K}$ is free over $F$ of rank $1$. Here a place of $F$ over $K$ is a valuation subring of $F$ which contains the image of $K$ under the structure map, is not all of $F$, and is a principal ideal ring. The conclusion is that the transcendence degree $\operatorname{trdeg}_K F$ equals $1$ (as a cardinal in Mathlib's `Algebra.trdeg`).
--
--   This is the classical fact that a one-variable algebraic function field over a perfect field has transcendence degree one, here derived from the differential and divisor-theoretic axioms packaged in `IsCurveOver`. It is used downstream in the treatment of intermediate fields of such an $F$ and in the good-reduction analysis of Jacobians.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_IsCurveOver_trdeg_eq_one.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.IsCurveOver.trdeg_eq_one
    (K F : Type*) [Field K] [Field F] [Algebra K F] [PerfectField K]
    [Algebra.EssFiniteType K F] [IsCurveOver K F] :
    Algebra.trdeg K F = 1 := by sorry
