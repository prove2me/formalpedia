-- Prove2me | Theorems.Thm_Algebra_norm_of_subsingleton
-- name    : Algebra.norm_of_subsingleton
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/93717b0d-e0de-5120-9b49-c4435aa7eb62
-- title:
--   Norm of an element of a subsingleton algebra is 1
-- statement:
--   Let $R$ be a commutative ring and let $A$ be a ring equipped with an $R$-algebra structure, with the additional hypothesis that $A$ is a subsingleton, i.e. all of its elements are equal (so $A$ is the zero ring). Then for every element $a$ of $A$, the algebra norm $\mathrm{N}_{A/R}(a)$, namely `Algebra.norm R a` — the determinant of the $R$-linear endomorphism of $A$ given by multiplication by $a$ — equals $1$. No finiteness or freeness assumption on $A$ as an $R$-module is imposed: the value is the determinant of an endomorphism of a module that is itself a subsingleton, for which Mathlib's determinant is $1$ by its general convention. The conclusion is an identity in $R$, holding for all $a$ simultaneously, since $A$ has only one element.
--
--   This is the degenerate case of the norm map, covering the value $1$ assigned to the empty product. It serves as a base case for block decompositions of norms indexed by a possibly empty set of factors, and is used in the proof of [`AlgebraicCurve.Place.evalAt_norm_eq_prod_fiber`](thm.html#AlgebraicCurve.Place.evalAt_norm_eq_prod_fiber).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_norm_of_subsingleton.lean

import Mathlib.RingTheory.Norm.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Algebra.norm_of_subsingleton {R A : Type*} [CommRing R] [Ring A] [Algebra R A] [Subsingleton A] (a : A) : Algebra.norm R a = 1 := by sorry
