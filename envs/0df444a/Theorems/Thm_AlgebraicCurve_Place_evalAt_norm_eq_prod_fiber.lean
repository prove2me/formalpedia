-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_evalAt_norm_eq_prod_fiber
-- name    : AlgebraicCurve.Place.evalAt_norm_eq_prod_fiber
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/f7afb460-a495-5739-9f09-6af8e676c20c
-- title:
--   Value of a norm as a weighted product over the fibre
-- statement:
--   Let $K$, $F$, $F'$ be fields with $F$ and $F'$ algebras over $K$ and $F'$ an algebra over $F$ compatibly with these structures, and assume $F'/F$ is finite and separable. Assume also that $F'/K$ has principal divisors, i.e. every nonzero $g \in F'$ admits a finitely supported integer-valued function $D$ on the places of $F'/K$ with $D(w) = \operatorname{ord}_w g$ for every $w$ and of degree $0$. Here a place of $F/K$ is a valuation subring of $F$, distinct from $F$, containing the image of $K$ and a principal ideal ring; $\operatorname{ord}_v$ is minus the logarithm of the associated adic valuation; $v$ is called rational when $K$ surjects onto its residue field, and then $\operatorname{ev}_v(h)$ is the element of $K$ representing the residue class of $h$ when $h$ lies in the valuation ring, and $0$ otherwise. Let $v$ be a place of $F/K$, let $f \in F'$ be nonzero, suppose $v$ is rational, and suppose that every place $w$ in the (finite) fibre of $v$ in $F'$, that is every $w$ restricting to $v$, is rational and satisfies $\operatorname{ord}_w f = 0$. Then $$\operatorname{ev}_v\big(N_{F'/F}(f)\big) = \prod_{w \mid v} \operatorname{ev}_w(f)^{\,e(w/F)},$$ where $e(w/F)$ is the least positive integer $n$ for which $\operatorname{ord}_w(\iota(g)) = n$ for some nonzero $g \in F$, $\iota$ the structure map $F \to F'$.
--
--   This is the multiplicative companion of the additive norm formula $\operatorname{ord}_v(N_{F'/F} h) = \sum_{w \mid v} f(w/v)\operatorname{ord}_w h$ for a finite separable extension of function fields: at a rational place with rational, unramified-in-value fibre, the value of the norm is the product of the values over the fibre weighted by ramification indices. It supports the pullback formula for evaluation of divisors, [`AlgebraicCurve.Divisor.evalFun_pullback`](thm.html#AlgebraicCurve.Divisor.evalFun_pullback), and is used in the place-specialisation computations on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_evalAt_norm_eq_prod_fiber.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_DivisorPushPull

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Place.evalAt_norm_eq_prod_fiber {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [HasPrincipalDivisors K F'] (v : Place K F) (f : F') (hf : f ≠ 0) (hv : v.IsRational) (hrat : ∀ w ∈ v.fiber F', Place.IsRational w) (hord : ∀ w ∈ v.fiber F', w.ord f = 0) : v.evalAt (Algebra.norm F f) = ∏ w ∈ v.fiber F', w.evalAt f ^ (w.ramificationIndex F) := by sorry
