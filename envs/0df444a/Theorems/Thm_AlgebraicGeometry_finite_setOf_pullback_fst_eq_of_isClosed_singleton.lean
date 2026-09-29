-- Prove2me | Theorems.Thm_AlgebraicGeometry_finite_setOf_pullback_fst_eq_of_isClosed_singleton
-- name    : AlgebraicGeometry.finite_setOf_pullback_fst_eq_of_isClosed_singleton
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/cba4fe6e-660d-5e79-b70b-c7edc56b7323
-- title:
--   Finiteness of the fibre over a closed point after base field extension
-- statement:
--   Let $\kappa$ and $\Omega$ be fields in the same universe with $\Omega$ a $\kappa$-algebra, let $X$ be a scheme and let $f \colon X \to \operatorname{Spec} \kappa$ be a morphism that is locally of finite type. Let $z$ be a point of $X$ whose singleton $\{z\}$ is closed in the underlying topological space of $X$. Form the base change of $f$ along the morphism $\operatorname{Spec} \Omega \to \operatorname{Spec} \kappa$ induced by the structure map $\kappa \to \Omega$, i.e. the pullback of $f$ and that morphism in the category of schemes, and let $\pi$ denote the first projection from this pullback to $X$. The assertion is that the set of points $w$ of the pullback with $\pi(w) = z$ is a finite subset of the underlying space of the pullback; equivalently, the set-theoretic fibre $\pi^{-1}(z)$ of the projection $X_\Omega \to X$ over the closed point $z$ is finite.
--
--   This is the standard fact that a closed point of a scheme locally of finite type over a field has a finite residue extension, so that its preimage in any base change to an extension field is $\operatorname{Spec}$ of an artinian ring and hence finite. It is used to transport finiteness statements about singular or crossing loci from a special fibre over $\kappa$ to the corresponding geometric fibre, in the finiteness lemma for the two-chart integral model and in the construction of curve models for $X_1(p)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_finite_setOf_pullback_fst_eq_of_isClosed_singleton.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.finite_setOf_pullback_fst_eq_of_isClosed_singleton
    {κ Ω : Type u} [Field κ] [Field Ω] [Algebra κ Ω]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of κ)) [LocallyOfFiniteType f]
    (z : X) (hz : IsClosed ({z} : Set X)) :
    {w : ↥(Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap κ Ω)))) |
      (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap κ Ω)))) w = z}.Finite := by sorry
