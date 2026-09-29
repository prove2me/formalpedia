-- Prove2me | Theorems.Thm_AlgebraicGeometry_eq_specMap_comp_pointOfClosedPoint_of_apply_closedPoint_eq
-- name    : AlgebraicGeometry.eq_specMap_comp_pointOfClosedPoint_of_apply_closedPoint_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/18dfeb2d-6695-53ba-8e40-02bb06f090c7
-- title:
--   K-points through a closed point are base changes of k-points
-- statement:
--   Let $k$ be an algebraically closed field and $K$ a field (both in the same universe), and let $\iota : k \to K$ be a ring homomorphism. Let $X$ be a scheme and $f : X \to \operatorname{Spec} k$ a morphism that is locally of finite type. Let $p : \operatorname{Spec} K \to X$ be a morphism lying over $\iota$, in the sense that $p$ followed by $f$ equals $\operatorname{Spec}$ of $\iota$, and let $x$ be a point of the underlying space of $X$ whose singleton $\{x\}$ is closed. Assume that the map on underlying spaces induced by $p$ sends the unique (closed) point of $\operatorname{Spec} K$ to $x$. Then $p$ equals $\operatorname{Spec}$ of $\iota$ followed by `AlgebraicGeometry.pointOfClosedPoint f x hx`, the $k$-point $\operatorname{Spec} k \to X$ attached to the closed point $x$ via the canonical isomorphism between $k$ and the residue field $\kappa(x)$. In other words, every $K$-valued point of $X$ over $k$ whose image is a closed point is obtained from the corresponding $k$-valued point by the base change $\operatorname{Spec} K \to \operatorname{Spec} k$.
--
--   This is the scheme-theoretic statement that, over an algebraically closed base field and for a morphism locally of finite type, closed points have residue field $k$ and hence a $K$-valued point supported at a closed point is rigid: it is determined by that point. It is used in the Čerednik–Drinfel'd part of the development, in the density statements for sets of points of the relevant curves for which a place composed with a degeneracy map agrees with a prescribed point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_eq_specMap_comp_pointOfClosedPoint_of_apply_closedPoint_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.eq_specMap_comp_pointOfClosedPoint_of_apply_closedPoint_eq
    {k K : Type u} [Field k] [IsAlgClosed k] [Field K] (ι : k →+* K)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (p : Spec (.of K) ⟶ X) (hp : p ≫ f = Spec.map (CommRingCat.ofHom ι))
    (x : ↥X) (hx : IsClosed ({x} : Set ↥X)) (hpx : p.base (IsLocalRing.closedPoint K) = x) :
    p = Spec.map (CommRingCat.ofHom ι) ≫ AlgebraicGeometry.pointOfClosedPoint f x hx := by sorry
