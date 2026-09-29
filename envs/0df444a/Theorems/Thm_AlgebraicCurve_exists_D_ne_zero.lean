-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_D_ne_zero
-- name    : AlgebraicCurve.exists_D_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/ed2d49c9-94e4-540f-94a3-7e2ee2d7c9ac
-- title:
--   Existence of a separating element on a curve
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and assume the predicate [`AlgebraicCurve.IsCurveOver K F`](def/AlgebraicCurve_IsCurveOver.html#L15), that is: (i) every nonzero $f \in F$ admits a divisor $D$ on the places of $F$ over $K$ with $D(v) = \operatorname{ord}_v(f)$ at every place $v$ and $\deg D = 0$, where a place is a valuation subring of $F$ that contains the image of $K$ under the structure map, is not all of $F$, and is a principal ideal ring; (ii) for every such place $v$ the residue field of the corresponding local ring is a finite-dimensional $K$-module; and (iii) the module of Kähler differentials $\Omega[F\!\restriction\!K]$ is free of rank one over $F$. The conclusion is that there exists $t \in F$ with $\mathrm{D}_{K,F}(t) \neq 0$ in $\Omega[F\!\restriction\!K]$, where $\mathrm{D}_{K,F}$ denotes the universal $K$-derivation $F \to \Omega[F\!\restriction\!K]$. No hypothesis on the characteristic is imposed.
--
--   This is the existence of a separating element for a function field of one variable, in the form that the universal derivation does not vanish identically. It is the starting point for the differential-theoretic part of the curve theory developed here, and is invoked in the construction of the Cartier operator and in its compatibility with constant field extensions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_D_ne_zero.lean

import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.exists_D_ne_zero {K F : Type*} [Field K] [Field F] [Algebra K F]
    [AlgebraicCurve.IsCurveOver K F] : ∃ t : F, KaehlerDifferential.D K F t ≠ 0 := by sorry
