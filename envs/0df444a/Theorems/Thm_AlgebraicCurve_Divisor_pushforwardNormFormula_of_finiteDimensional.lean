-- Prove2me | Theorems.Thm_AlgebraicCurve_Divisor_pushforwardNormFormula_of_finiteDimensional
-- name    : AlgebraicCurve.Divisor.pushforwardNormFormula_of_finiteDimensional
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/ce50b8ce-78ea-58f1-98b8-b5b0947e1d6c
-- title:
--   Push-forward of a principal divisor is the divisor of the norm
-- statement:
--   Let $K \subseteq F \subseteq F'$ be fields, with $F$ and $F'$ $K$-algebras and $F'$ an $F$-algebra forming a scalar tower over $K$, such that $F'$ is finite-dimensional and separable over $F$, and $F$ has characteristic zero. Here a place of a field extension $L/K$ is a valuation subring of $L$ that contains the image of $K$, is not all of $L$, and is a principal ideal ring; a divisor is a finitely supported function from places to $\mathbb{Z}$; and the push-forward of a divisor on $F'$ is the additive map sending the basis element at a place $w$ to the place $w|_F$ of $F/K$ with multiplicity the inertia degree of $w$ over $F$. The theorem asserts `Divisor.PushforwardNormFormula K F F'`: for every nonzero $f \in F'$, every divisor $D$ on $F'$ satisfying $D(w) = \operatorname{ord}_w(f)$ at every place $w$ of $F'/K$, and every place $v$ of $F/K$, the value of the push-forward of $D$ at $v$ equals $\operatorname{ord}_v\bigl(N_{F'/F}(f)\bigr)$. Note that the divisor $D$ enters only through the hypothesis that its values are the orders of $f$, so the conclusion is the identity $\pi_*(\operatorname{div} f)(v) = \operatorname{ord}_v(N_{F'/F} f)$ conditional on such a $D$ existing.
--
--   This is the standard compatibility of proper push-forward with principal divisors, in the form $\pi_*\operatorname{div}(f) = \operatorname{div}(N_{F'/F}f)$ for a finite separable extension of function fields, stated without any hypothesis guaranteeing that orders define a divisor globally. It is the form used to deduce that principal divisors have degree zero by pushing forward to a rational function field, and it feeds the divisor bookkeeping on models of modular curves used later in the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Divisor_pushforwardNormFormula_of_finiteDimensional.lean

import Definitions.Def_AlgebraicCurve_PlacesOverDVR

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Divisor.pushforwardNormFormula_of_finiteDimensional {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [CharZero F] :
    Divisor.PushforwardNormFormula K F F' := by sorry
