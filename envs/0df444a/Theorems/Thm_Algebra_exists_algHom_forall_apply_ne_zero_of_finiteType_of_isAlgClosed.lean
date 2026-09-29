-- Prove2me | Theorems.Thm_Algebra_exists_algHom_forall_apply_ne_zero_of_finiteType_of_isAlgClosed
-- name    : Algebra.exists_algHom_forall_apply_ne_zero_of_finiteType_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/a77c9c1c-c4f7-5fc5-929f-7154a9d756ea
-- title:
--   Rational points avoiding finitely many non-zero functions
-- statement:
--   Let $k$ be an algebraically closed field, and let $B$ be a commutative ring which is an integral domain, equipped with a $k$-algebra structure, and of finite type as a $k$-algebra (i.e. a quotient of a polynomial ring in finitely many variables over $k$). Let $\iota$ be a finite index type and let $g : \iota \to B$ be a family of elements of $B$ with $g_i \neq 0$ for every $i$. Then there exists a $k$-algebra homomorphism $\chi : B \to k$ such that $\chi(g_i) \neq 0$ for every $i$. In geometric terms: the affine $k$-variety $\operatorname{Spec} B$ has a $k$-rational point lying outside the vanishing loci of all the $g_i$. Note that the conclusion asserts the existence of a homomorphism to $k$ itself, not merely to some extension field, and that no separate non-triviality hypothesis on $B$ is needed, since $B$ is assumed to be a domain.
--
--   This is the form of the weak Nullstellensatz (Zariski's lemma together with the density of rational points on an irreducible affine variety over an algebraically closed field) used in the project: a $k$-point of $\operatorname{Spec} B$ avoiding the zero sets of finitely many prescribed non-zero functions. It is cited in the construction of a ring isomorphism onto a closure in [`AlgebraicCurve.exists_ringEquiv_closure_of_support_correspondence_single_eq_of_essFiniteType`](thm.html#AlgebraicCurve.exists_ringEquiv_closure_of_support_correspondence_single_eq_of_essFiniteType), where a point at which several non-vanishing conditions hold simultaneously is required.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_exists_algHom_forall_apply_ne_zero_of_finiteType_of_isAlgClosed.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Algebra.exists_algHom_forall_apply_ne_zero_of_finiteType_of_isAlgClosed
    {k : Type*} [Field k] [IsAlgClosed k]
    {B : Type*} [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B]
    {ι : Type*} [Finite ι] (g : ι → B) (hg : ∀ i, g i ≠ 0) :
    ∃ χ : B →ₐ[k] k, ∀ i, χ (g i) ≠ 0 := by sorry
