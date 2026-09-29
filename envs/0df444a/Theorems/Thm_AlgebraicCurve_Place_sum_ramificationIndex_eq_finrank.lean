-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_sum_ramificationIndex_eq_finrank
-- name    : AlgebraicCurve.Place.sum_ramificationIndex_eq_finrank
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/3e43ec68-b2d4-5d4a-8402-57af3e934b7e
-- title:
--   Rational fibres: sum_{w∣ v} e(w∣ v) = [F':F]
-- statement:
--   Let $K \subseteq F \subseteq F'$ be fields, with $F$ and $F'$ algebras over $K$ and $F'$ an algebra over $F$ compatibly (a scalar tower), such that $F'$ is finite-dimensional and separable over $F$, and such that $F'/K$ has principal divisors: for every $f \in F'$ with $f \neq 0$ there is a finitely supported function $D$ on the places of $F'/K$ with $D(w) = \mathrm{ord}_w(f)$ for every place $w$ and $\deg D = 0$. Here a place of $F/K$ is a valuation subring of $F$ containing the image of $K$, different from $F$ itself, and a principal ideal ring. Let $v$ be such a place of $F/K$, and assume $v$ is rational, meaning that the structure map from $K$ to the residue field of $v$ is surjective, and that every place $w$ of $F'/K$ lying in the fibre of $v$ (the finite set of places of $F'$ restricting to $v$) is likewise rational. Then the sum over $w$ in the fibre of $v$ of the ramification indices $e(w \mid F)$, each being the least positive integer of the form $\mathrm{ord}_w(f)$ for some nonzero $f \in F$, equals $[F' : F]$, as an identity in $\mathbb{Z}$.
--
--   This is the fundamental equality $\sum_{w \mid v} e(w\mid v) f(w \mid v) = [F':F]$ of function-field theory, specialised to a fibre in which all residue degrees are $1$; geometrically, a degree-$n$ cover has $n$ points over a rational point, counted with multiplicity. It is used in the function-field foundations of the project, for instance in computing the cardinality of a fibre over a place where some function has order one, in summing orders along a fibre, and towards Weil reciprocity for a finite separable extension $F'/F$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_sum_ramificationIndex_eq_finrank.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_DivisorPushPull

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Place.sum_ramificationIndex_eq_finrank {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [HasPrincipalDivisors K F'] (v : Place K F) (hv : v.IsRational) (hrat : ∀ w ∈ v.fiber F', Place.IsRational w) : ∑ w ∈ v.fiber F', (w.ramificationIndex F : ℤ) = (Module.finrank F F' : ℤ) := by sorry
