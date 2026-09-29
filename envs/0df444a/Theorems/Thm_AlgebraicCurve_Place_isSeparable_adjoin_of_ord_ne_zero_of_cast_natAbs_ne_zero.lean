-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_isSeparable_adjoin_of_ord_ne_zero_of_cast_natAbs_ne_zero
-- name    : AlgebraicCurve.Place.isSeparable_adjoin_of_ord_ne_zero_of_cast_natAbs_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/e0282944-4f70-518e-b478-7a7335a5d65c
-- title:
--   Elements of tame nonzero order are separating
-- statement:
--   Let $K$ and $F$ be fields with $K$ perfect and $F$ a $K$-algebra, and suppose there is an element $x \in F$ such that $F$ is algebraic over the intermediate field $K(x) =$ `IntermediateField.adjoin K {x}`. Let $v$ be a place of $F$ over $K$ in the sense of [`AlgebraicCurve.Place K F`](def/AlgebraicCurve_DivisorClassGroup.html#L22), that is, a valuation subring of $F$ containing the image of $K$, distinct from all of $F$, and a principal ideal ring; write $\operatorname{ord}_v$ for the associated order function, defined as minus the logarithm of the $\mathbb{Z}^{m0}$-valued adic valuation attached to the height-one prime of that valuation ring. Let $t \in F$ satisfy $\operatorname{ord}_v(t) \neq 0$ and suppose the image in $K$ of the natural number $|\operatorname{ord}_v(t)|$ is nonzero, i.e. the absolute value of the order of $t$ at $v$ is prime to the characteristic of $K$ (a vacuous condition in characteristic $0$). The conclusion is that $F$ is a separable algebraic extension of the intermediate field $K(t) =$ `IntermediateField.adjoin K {t}`; in particular $t$ is a separating element of $F/K$.
--
--   This is the classical criterion for an element of a one-variable function field over a perfect constant field to be separating: an element whose order at some place is nonzero and tame generates a subfield over which the function field is separable. It is used, via its divisor-class-group variant, in the construction of models of modular curves, where elements of prescribed tame order at a cusp are needed to produce formally unramified quotients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_isSeparable_adjoin_of_ord_ne_zero_of_cast_natAbs_ne_zero.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Differentials
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped IntermediateField

theorem AlgebraicCurve.Place.isSeparable_adjoin_of_ord_ne_zero_of_cast_natAbs_ne_zero
    {K F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F]
    (v : AlgebraicCurve.Place K F) {t : F} (ht : v.ord t ≠ 0) (htame : (((v.ord t).natAbs : ℕ) : K) ≠ 0) :
    Algebra.IsSeparable (IntermediateField.adjoin K ({t} : Set F)) F := by sorry
