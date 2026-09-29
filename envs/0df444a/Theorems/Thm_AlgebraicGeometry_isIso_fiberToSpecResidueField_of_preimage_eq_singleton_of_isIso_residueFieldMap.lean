-- Prove2me | Theorems.Thm_AlgebraicGeometry_isIso_fiberToSpecResidueField_of_preimage_eq_singleton_of_isIso_residueFieldMap
-- name    : AlgebraicGeometry.isIso_fiberToSpecResidueField_of_preimage_eq_singleton_of_isIso_residueFieldMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/2da96f98-b334-5a1f-8b58-868032d333fc
-- title:
--   Unramified morphism: fibre at a point with trivial residue extension
-- statement:
--   Let $U$ and $S$ be schemes (in a fixed universe) and let $f\colon U\to S$ be a morphism that is locally of finite type and formally unramified. Let $x$ be a point of $U$ and assume that $x$ is the only point of $U$ lying over $s:=f(x)$, i.e. every $y\in U$ with $f(y)=f(x)$ equals $x$; assume further that the induced map on residue fields $\kappa(s)\to\kappa(x)$, the morphism `f.residueFieldMap x`, is an isomorphism. The conclusion is that the canonical morphism from the scheme-theoretic fibre of $f$ over $s$, namely the pullback of $f$ along $\operatorname{Spec}\kappa(s)\to S$, to $\operatorname{Spec}\kappa(s)$ is an isomorphism; equivalently, $U\times_S\operatorname{Spec}\kappa(s)\cong\operatorname{Spec}\kappa(s)$ via the projection. Note that the hypothesis on residue fields is formulated for the morphism of residue fields at $x$ itself, and that no separatedness, quasi-compactness or finiteness assumption beyond local finiteness of type is imposed.
--
--   This is the standard local description of unramified morphisms: over a point with a unique preimage and trivial residue field extension the fibre of a locally of finite type, formally unramified (e.g. étale) morphism is the reduced one-point scheme $\operatorname{Spec}\kappa(s)$. It is used in the project by [`V3Asm.exc_rational`](thm.html#V3Asm.exc_rational) and [`V3AsmLevel.exc_rational`](thm.html#V3AsmLevel.exc_rational), where it yields rationality of a distinguished point over the base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isIso_fiberToSpecResidueField_of_preimage_eq_singleton_of_isIso_residueFieldMap.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.isIso_fiberToSpecResidueField_of_preimage_eq_singleton_of_isIso_residueFieldMap
    {U S : Scheme.{u}} (f : U ⟶ S) [LocallyOfFiniteType f] [FormallyUnramified f]
    (x : U) (hx : ∀ y : U, f y = f x → y = x) [IsIso (f.residueFieldMap x)] :
    IsIso (f.fiberToSpecResidueField (f x)) := by sorry
