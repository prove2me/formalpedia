-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_kaehlerD_ne_zero_of_ord_eq_one
-- name    : AlgebraicCurve.Place.kaehlerD_ne_zero_of_ord_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/b296f291-0047-57f8-8ac9-36e7497748f0
-- title:
--   A uniformizer has non-zero differential over a perfect constant field
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra and $K$ perfect, and let $x \in F$ be such that $F$ is algebraic over the intermediate field $K(x)$ obtained by adjoining $x$ to $K$ inside $F$. Let $v$ be a place of $F$ over $K$, that is, a valuation subring of $F$ which contains the image of $K$ under the structure map, is not all of $F$, and is a principal ideal ring. For $f \in F$ write $\operatorname{ord}_v(f)$ for the integer $-\log$ of the value of $f$ under the $\mathbb{Z}^{m0}$-valued adic valuation attached to the height-one prime of $v$, so that $\operatorname{ord}_v$ is the normalised additive valuation of $v$. Then for any $t \in F$ with $\operatorname{ord}_v(t) = 1$, the universal derivation $d : F \to \Omega^1_{F/K}$ of the module of Kähler differentials satisfies $dt \neq 0$.
--
--   Classically this says that an element of order one at a place of a function field with perfect constant field is a separating element, so its differential is non-zero; the hypothesis on $x$ records that $F/K$ is algebraic over a simple transcendental (or algebraic) extension. It is used throughout the differential-theoretic part of the curve machinery, for instance in the construction of local expansions at a place and in the comparison of fibre cardinalities with local degrees.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_kaehlerD_ne_zero_of_ord_eq_one.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AlgebraicCurve.Place.kaehlerD_ne_zero_of_ord_eq_one {K F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F] (v : AlgebraicCurve.Place K F) {t : F} (ht : v.ord t = 1) :
    KaehlerDifferential.D K F t ≠ 0 := by sorry
