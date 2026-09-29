-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_ord_norm_eq_zero_of_forall_fiber
-- name    : AlgebraicCurve.Place.ord_norm_eq_zero_of_forall_fiber
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/7e1f30e5-1112-5b1b-999b-a148573201b7
-- title:
--   Norm has trivial order at v when f is a unit above v
-- statement:
--   Let $K \subseteq F \subseteq F'$ be fields, with $F$ a $K$-algebra, $F'$ a $K$-algebra and an $F$-algebra compatibly (a scalar tower), $F'/F$ finite and separable, and $F$ of characteristic zero; assume moreover that $F'/K$ has principal divisors, i.e. every nonzero $g \in F'$ admits a finitely supported function $D$ on the places of $F'/K$ with $D(w) = \operatorname{ord}_w(g)$ for all $w$ and $\deg D = 0$. Here a place of $F/K$ is a valuation subring of $F$ containing the image of $K$, distinct from $F$ itself and a principal ideal ring, and $\operatorname{ord}_v$ is the negative of the logarithm of the associated $\mathbb{Z}^{m0}$-valued adic valuation. Let $f \in F'$ be nonzero and let $v$ be a place of $F/K$ such that $\operatorname{ord}_w(f) = 0$ for every $w$ in the fibre of $v$ in the places of $F'/K$ (a finite set). The conclusion is that $\operatorname{ord}_v\bigl(N_{F'/F}(f)\bigr) = 0$, where $N_{F'/F}$ is the algebra norm: the norm of $f$ has neither a zero nor a pole at $v$.
--
--   This is the standard consequence of the norm formula for orders in a finite separable extension of function fields: a function that is a unit at every place above $v$ has norm a unit at $v$. It is used in the proof of Weil reciprocity along a finite separable extension, where it transfers disjointness of divisors upstairs to disjointness downstairs, and is cited by [`AlgebraicCurve.weilReciprocity_algebraMap`](thm.html#AlgebraicCurve.weilReciprocity_algebraMap).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_ord_norm_eq_zero_of_forall_fiber.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_DivisorPushPull

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Place.ord_norm_eq_zero_of_forall_fiber {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [CharZero F] [HasPrincipalDivisors K F'] {f : F'} (hf : f ≠ 0) (v : Place K F) (h : ∀ w ∈ v.fiber F', w.ord f = 0) : v.ord (Algebra.norm F f) = 0 := by sorry
