-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_transcendental_of_ord_ne_zero
-- name    : AlgebraicCurve.Place.transcendental_of_ord_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/5d81da8b-db85-502b-a949-6ed3c5d7e14b
-- title:
--   Nonzero order at a place forces transcendence
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $v$ be a place of $F$ over $K$ in the sense of the project's structure `Place`: a valuation subring $\mathcal{O}_v \subseteq F$ which contains the image of $K$ under the structure map, is not the whole of $F$, and is a principal ideal ring. For $f \in F$ the integer $v.\mathrm{ord}\,f$ is defined as the negative of the logarithm of the value of $f$ under the adic valuation of $F$ attached to the height-one prime of $\mathcal{O}_v$, with values in $\mathbb{Z}^{m0}$. The assertion is that for $t \in F$ with $v.\mathrm{ord}\,t \neq 0$, the element $t$ is transcendental over $K$, i.e. `Transcendental K t` holds: $t$ is not a root of any nonzero polynomial with coefficients in $K$. No hypothesis is imposed on the extension $F/K$ beyond those packaged in `Place`, and no assumption on the characteristic is made.
--
--   This is the contrapositive of the classical fact that elements algebraic over the constant field have neither zeros nor poles, so order zero at every place; in particular a uniformiser, having order $1$, is transcendental over $K$. It is used throughout the surrounding theory of places, divisors and differentials of a curve, for instance when exhibiting transcendental elements with prescribed residue behaviour and when comparing regular differentials under a constant field extension.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_transcendental_of_ord_ne_zero.lean

import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Mathlib.RingTheory.Algebraic.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.Place.transcendental_of_ord_ne_zero {K F : Type*} [Field K] [Field F] [Algebra K F] (v : AlgebraicCurve.Place K F) {t : F} (ht : v.ord t ≠ 0) :
    Transcendental K t := by sorry
