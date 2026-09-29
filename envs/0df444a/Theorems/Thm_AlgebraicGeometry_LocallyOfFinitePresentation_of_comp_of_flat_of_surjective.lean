-- Prove2me | Theorems.Thm_AlgebraicGeometry_LocallyOfFinitePresentation_of_comp_of_flat_of_surjective
-- name    : AlgebraicGeometry.LocallyOfFinitePresentation.of_comp_of_flat_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/19675729-ef32-5370-a4bd-6dec315e5afb
-- title:
--   Finite presentation descends along flat quasi-compact surjections
-- statement:
--   Let $X$, $Y$, $Z$ be schemes in a fixed universe, and let $f : X \to Y$ and $g : Y \to Z$ be morphisms of schemes. Assume that $f$ is flat, locally of finite presentation, surjective and quasi-compact, and that the composite $f$ followed by $g$, i.e. $g \circ f : X \to Z$, is locally of finite presentation. The conclusion is that $g$ itself is locally of finite presentation. All four hypotheses on $f$, and the hypothesis on the composite, are carried as instance arguments in the Mathlib sense, so the statement is phrased entirely in Mathlib's language for morphism properties of schemes; no property of $Z$ or of the base is assumed, and the result is stated over an arbitrary base.
--
--   This is the statement that being locally of finite presentation is local on the source for the fppf topology (with a quasi-compactness hypothesis used to reduce to finitely many affines), in the form of descent along a flat, quasi-compact, surjective morphism locally of finite presentation. It is used to deduce the analogous descent statement for smoothness, [`AlgebraicGeometry.Smooth.of_comp_of_smooth_of_surjective`](thm.html#AlgebraicGeometry.Smooth.of_comp_of_smooth_of_surjective), and from there in the construction of Drinfeld-type global models of Weierstrass curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_LocallyOfFinitePresentation_of_comp_of_flat_of_surjective.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.LocallyOfFinitePresentation.of_comp_of_flat_of_surjective
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [Flat f] [LocallyOfFinitePresentation f] [Surjective f]
    [QuasiCompact f] [LocallyOfFinitePresentation (f ≫ g)] : LocallyOfFinitePresentation g := by sorry
