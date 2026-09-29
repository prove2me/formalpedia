-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_exists_isIntegral_adjoin_and_ord_eq_one_and_forall_ord_eq_zero
-- name    : AlgebraicCurve.Place.exists_isIntegral_adjoin_and_ord_eq_one_and_forall_ord_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/50728c49-b0a8-5e21-a80e-70bc6600db77
-- title:
--   Moving lemma for places of a function field
-- statement:
--   Let $k$ and $F$ be fields with $F$ a $k$-algebra, and let $x \in F$ be transcendental over $k$, such that $F$ is a finite-dimensional and separable extension of the intermediate field $k(x) =$ `IntermediateField.adjoin k {x}`. A place of $F/k$ is, in this development, a valuation subring $\mathcal{O}_Q \subseteq F$ that contains the image of $k$ under the structure map, is not all of $F$, and is a principal ideal ring; its $\operatorname{ord}_Q$ is the negative of the logarithm of the $\mathbb{Z}^{m0}$-valued valuation attached to the height-one prime of $\mathcal{O}_Q$, so $\operatorname{ord}_Q$ is the normalised discrete valuation of $\mathcal{O}_Q$. Let $S$ be a finite set of such places, let $P \in S$, and assume $x \in \mathcal{O}_Q$ for every $Q \in S$. The conclusion asserts the existence of $y \in F$ that is integral over the subalgebra $k[x] =$ `Algebra.adjoin k {x}` and satisfies $\operatorname{ord}_P(y) = 1$ together with $\operatorname{ord}_Q(y) = 0$ for every $Q \in S$ with $Q \neq P$.
--
--   This is a moving lemma, or weak approximation statement, inside the finite holomorphy ring of the function field $F/k$ relative to the transcendental element $x$: one produces a function, integral over $k[x]$, with a simple zero at a prescribed place of the finite set $S$ and no zero or pole at the remaining ones. It is used in the construction of regular prolongations, where such a $y$ serves as a uniformiser adapted to a finite set of places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_exists_isIntegral_adjoin_and_ord_eq_one_and_forall_ord_eq_zero.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Place.exists_isIntegral_adjoin_and_ord_eq_one_and_forall_ord_eq_zero
    {k F : Type*} [Field k] [Field F] [Algebra k F] (x : F) (hx : Transcendental k x)
    [FiniteDimensional (IntermediateField.adjoin k ({x} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin k ({x} : Set F)) F]
    (S : Finset (Place k F)) (P : Place k F) (hP : P ∈ S)
    (hS : ∀ Q ∈ S, x ∈ Q.toValuationSubring) :
    ∃ y : F, IsIntegral (Algebra.adjoin k ({x} : Set F)) y ∧ P.ord y = 1 ∧
      ∀ Q ∈ S, Q ≠ P → Q.ord y = 0 := by sorry
