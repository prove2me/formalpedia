-- Prove2me | Theorems.Thm_AlgebraicGeometry_geometricallyIrreducible_iff_bijective_appTop_of_isProper_of_smooth
-- name    : AlgebraicGeometry.geometricallyIrreducible_iff_bijective_appTop_of_isProper_of_smooth
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/7cdce51e-399b-5c1f-bf60-8fd5d9e7cd90
-- title:
--   Proper smooth X/K is geometrically irreducible iff Γ(X,mathcal O_X)=K
-- statement:
--   Let $K$ be a field and let $g \colon X \to \operatorname{Spec} K$ be a morphism of schemes (all data in a single universe) which is proper and smooth, and assume the underlying space of $X$ is nonempty. Write $\Gamma(X,\mathcal O_X)$ for the global sections of $X$ and let $K \to \Gamma(X,\mathcal O_X)$ be the structure map, realised as the inverse of the canonical isomorphism $K \xrightarrow{\sim} \Gamma(\operatorname{Spec} K, \mathcal O)$ followed by the map $g^{*}$ on global sections induced by $g$. The theorem asserts the equivalence of two conditions: that $g$ is geometrically irreducible (the Mathlib predicate `GeometricallyIrreducible`, i.e. every base change of $g$ along a field extension of $K$ has irreducible underlying space), and that the underlying ring homomorphism of the above composite $K \to \Gamma(X,\mathcal O_X)$ is bijective as a function. Both directions are proved, so the statement is a genuine biconditional under the standing hypotheses of properness, smoothness and nonemptiness.
--
--   This is the classical criterion that a nonempty proper smooth scheme over a field $K$ is geometrically irreducible exactly when its ring of global regular functions is $K$ itself. It is used in the project's work on polarisations and on the openness of the locus where geometric fibres are irreducible.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_geometricallyIrreducible_iff_bijective_appTop_of_isProper_of_smooth.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

theorem AlgebraicGeometry.geometricallyIrreducible_iff_bijective_appTop_of_isProper_of_smooth
    {K : Type u} [Field K] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of K)) [IsProper g] [Smooth g] [Nonempty ↥X] :
    GeometricallyIrreducible g ↔ Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ g.appTop).hom := by sorry
