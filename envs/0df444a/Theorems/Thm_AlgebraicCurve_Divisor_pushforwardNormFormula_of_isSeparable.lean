-- Prove2me | Theorems.Thm_AlgebraicCurve_Divisor_pushforwardNormFormula_of_isSeparable
-- name    : AlgebraicCurve.Divisor.pushforwardNormFormula_of_isSeparable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/bebd3c2f-3bcb-568b-bf69-355c5293b164
-- title:
--   Push-forward norm formula for finite separable extensions
-- statement:
--   Let $K$, $F$, $F'$ be fields with $F$ and $F'$ algebras over $K$ and $F'$ an algebra over $F$, the two $K$-structures being compatible (a scalar tower $K \subseteq F \subseteq F'$), with $F'$ finite-dimensional and separable over $F$. Assume further that $F'$ has principal divisors over $K$, i.e. for every $f \in F'$ with $f \neq 0$ there is a finitely supported function $D$ from the places of $F'$ over $K$ to $\mathbb{Z}$ with $D(w) = \operatorname{ord}_w(f)$ for every such place $w$ and with $\deg D = 0$; here a place of $F'$ over $K$ is a valuation subring of $F'$ containing the image of $K$, different from $F'$ itself, and a principal ideal ring. The conclusion is the predicate `Divisor.PushforwardNormFormula K F F'`: for every nonzero $f \in F'$, every divisor $D$ of $F'$ over $K$ satisfying $D(w) = \operatorname{ord}_w(f)$ at every place $w$ of $F'$, and every place $v$ of $F$ over $K$, the push-forward divisor of $D$ — whose value at $v$ is $\sum_{w} D(w)\,f(w/v)$, the sum over the places $w$ of $F'$ restricting to $v$, weighted by the inertia degree of $w$ over $F$ — equals $\operatorname{ord}_v\bigl(N_{F'/F}(f)\bigr)$.
--
--   This is the compatibility of the push-forward of divisors with the relative norm for a finite separable extension of function fields, with no restriction on the characteristic of the constant field. It is used for the push-forward of principal divisors and, through statements about orders of norms along fibres, in the analysis of the rational Tate module and its fixed fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Divisor_pushforwardNormFormula_of_isSeparable.lean

import Definitions.Def_AlgebraicCurve_DivisorPushPull

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Divisor.pushforwardNormFormula_of_isSeparable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [HasPrincipalDivisors K F'] : Divisor.PushforwardNormFormula K F F' := by sorry
