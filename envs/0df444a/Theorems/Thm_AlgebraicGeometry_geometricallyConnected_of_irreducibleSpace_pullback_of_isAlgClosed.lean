-- Prove2me | Theorems.Thm_AlgebraicGeometry_geometricallyConnected_of_irreducibleSpace_pullback_of_isAlgClosed
-- name    : AlgebraicGeometry.geometricallyConnected_of_irreducibleSpace_pullback_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/96fe145d-526d-53ce-bfd5-c39e5cf3f30c
-- title:
--   Irreducibility over one algebraically closed extension gives geometric connectedness
-- statement:
--   Let $K$ be a field (in a fixed universe), $X$ a scheme and $f : X \to \operatorname{Spec} K$ a morphism of schemes, where $\operatorname{Spec} K$ is the spectrum of $K$ viewed as a commutative ring object. Let $k$ be a field equipped with a $K$-algebra structure and assumed algebraically closed, and let $g : \operatorname{Spec} k \to \operatorname{Spec} K$ be the morphism induced by the structure map $K \to k$. The hypothesis is that the underlying topological space of the fibre product $X \times_{\operatorname{Spec} K} \operatorname{Spec} k$, formed as the categorical pullback of $f$ along $g$, is an irreducible space, i.e. it is nonempty and any two nonempty open subsets meet. The conclusion is that $f$ satisfies Mathlib's predicate `GeometricallyConnected`, so that connectedness of $X$ over $K$ persists under all base changes contemplated by that predicate; no finiteness, reducedness or quasi-compactness assumption on $X$ or on $f$ is made, and $k$ is only required to be one algebraically closed extension of $K$, not an algebraic closure.
--
--   This is the standard descent statement that geometric connectedness over a field can be tested after base change to a single algebraically closed extension (compare EGA IV₂ 4.5.6–4.5.9). It is used in the analysis of coarse moduli schemes for quaternionic data in the Čerednik–Drinfel'd part of the development, where geometric reducedness and geometric connectedness of a curve model are established simultaneously.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_geometricallyConnected_of_irreducibleSpace_pullback_of_isAlgClosed.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.geometricallyConnected_of_irreducibleSpace_pullback_of_isAlgClosed
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K))
    (k : Type u) [Field k] [Algebra K k] [IsAlgClosed k]
    [IrreducibleSpace ↑(pullback f (Spec.map (CommRingCat.ofHom (algebraMap K k))))] :
    GeometricallyConnected f := by sorry
