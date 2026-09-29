-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_ord_eq_zero_of_isAlgebraic
-- name    : AlgebraicCurve.Place.ord_eq_zero_of_isAlgebraic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/f0dd38e5-80be-53da-9394-8bd30a6bec4e
-- title:
--   Algebraic elements have order zero at every place
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $v$ be a place of $F$ over $K$ in the sense of the divisor-class-group vocabulary: a valuation subring of $F$ which contains the image of $K$ under the structure map, is not the whole of $F$, and is a principal ideal ring. Let $x \in F$ be algebraic over $K$, i.e. a root of a nonzero polynomial with coefficients in $K$. Then $v.\mathrm{ord}\,x = 0$, where $\mathrm{ord}$ is the integer-valued order function attached to $v$, namely $\mathrm{ord}\,f = -\log$ of the value of $f$ under the $\mathbb{Z}^{m0}$-valued adic valuation associated with the height-one prime of $v$'s valuation subring (with the convention, coming from the logarithm on $\mathbb{Z}^{m0}$, that $\mathrm{ord}\,0 = 0$, so that the assertion also covers the algebraic element $x = 0$). No finiteness, separability or characteristic hypothesis is imposed on $K \subseteq F$.
--
--   This is the statement that the constants of a function field, and more generally all elements algebraic over the base field, have neither zeros nor poles at any place. It underlies the degree theory of divisors and is used in the computations of divisor degrees and effective divisors, and in the results on constant field extensions for curves over finite fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_ord_eq_zero_of_isAlgebraic.lean

import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Mathlib.RingTheory.Algebraic.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.Place.ord_eq_zero_of_isAlgebraic {K F : Type*} [Field K] [Field F] [Algebra K F] (v : AlgebraicCurve.Place K F) {x : F} (hx : IsAlgebraic K x) :
    v.ord x = 0 := by sorry
