-- Prove2me | Theorems.Thm_AlgebraicGeometry_isFinite_of_finite_setOf_exists_section_of_isAlgClosed
-- name    : AlgebraicGeometry.isFinite_of_finite_setOf_exists_section_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/906832ec-fc6c-5a27-9e21-561cfc495a3d
-- title:
--   Finitely many k-points forces finiteness over an algebraically closed field
-- statement:
--   Let $k$ be an algebraically closed field, let $X$ be a scheme, and let $f \colon X \to \operatorname{Spec} k$ be a morphism which is locally of finite type. Consider the set of those points $x$ of the underlying topological space of $X$ for which there exists a morphism $s \colon \operatorname{Spec} k \to X$ with $s$ followed by $f$ equal to the identity of $\operatorname{Spec} k$ and with $s$ carrying the closed point of $\operatorname{Spec} k$ (the unique point of the spectrum of the field $k$, obtained as the closed point of $k$ viewed as a local ring) to $x$; that is, the set of points of $X$ that are images of $k$-rational points of $X$ over $k$. The hypothesis is that this set is finite. The conclusion is that $f$ is a finite morphism. No quasi-compactness, separatedness or finite-type (as opposed to locally-of-finite-type) hypothesis is imposed on $f$.
--
--   This is the scheme-theoretic form of the statement that a scheme locally of finite type over an algebraically closed field with only finitely many $k$-points is the spectrum of a finite-dimensional $k$-algebra; it rests on Jacobson-ness of schemes locally of finite type over a field and, through that, on the Hilbert Nullstellensatz. It is used to recognise finiteness of morphisms over algebraically closed fields, in particular by [`AlgebraicGeometry.isFinite_of_isProper_of_finite_setOf_comp_eq`](thm.html#AlgebraicGeometry.isFinite_of_isProper_of_finite_setOf_comp_eq) and in the analysis of kernels of isogenies on Néron models of modular curves at a prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isFinite_of_finite_setOf_exists_section_of_isAlgClosed.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.isFinite_of_finite_setOf_exists_section_of_isAlgClosed
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f]
    (hfin : {x : X | ∃ s : Spec (.of k) ⟶ X, s ≫ f = 𝟙 _ ∧ s (IsLocalRing.closedPoint k) = x}.Finite) :
    IsFinite f := by sorry
