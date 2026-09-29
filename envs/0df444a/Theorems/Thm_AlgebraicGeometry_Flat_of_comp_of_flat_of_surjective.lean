-- Prove2me | Theorems.Thm_AlgebraicGeometry_Flat_of_comp_of_flat_of_surjective
-- name    : AlgebraicGeometry.Flat.of_comp_of_flat_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/48262859-b51f-5004-9dc2-36bb91ec212e
-- title:
--   Flatness descends along flat surjective morphisms on the source
-- statement:
--   Let $X$, $U$, $Y$ be schemes (in a fixed universe), let $c : X \to U$ be a morphism of schemes which is flat and surjective, and let $p : U \to Y$ be a morphism of schemes such that the composite $c$ followed by $p$, i.e. $p \circ c : X \to Y$, is flat. Then $p$ is flat. Here flatness and surjectivity of morphisms are the Mathlib morphism properties `Flat` and `Surjective` for schemes, supplied as instance hypotheses, and the conclusion is the instance-shaped assertion that $p$ is flat. No quasi-compactness, separatedness, affineness or finite-presentation hypothesis is imposed on any of the three morphisms, and no hypothesis beyond flatness and surjectivity of $c$ is assumed: the statement is the fully general form of descent of flatness along a flat surjection on the source.
--
--   This is the assertion that flatness of a morphism of schemes is local on the source for the fpqc topology, in the form: flatness of $p$ may be tested after precomposition with a flat surjective morphism. It is used in the construction of fppf quotients of group-law slices and in the comparison of projective Weierstrass models under Frobenius.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Flat_of_comp_of_flat_of_surjective.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Flat.of_comp_of_flat_of_surjective {X U Y : Scheme.{u}} (c : X ⟶ U) [Flat c]
    [Surjective c] (p : U ⟶ Y) [Flat (c ≫ p)] : Flat p := by sorry
