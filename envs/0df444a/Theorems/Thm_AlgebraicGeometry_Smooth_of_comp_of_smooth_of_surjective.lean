-- Prove2me | Theorems.Thm_AlgebraicGeometry_Smooth_of_comp_of_smooth_of_surjective
-- name    : AlgebraicGeometry.Smooth.of_comp_of_smooth_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/18d7ecf2-ac28-51f6-bbef-e762ef7eef9b
-- title:
--   Smoothness descends along a smooth quasi-compact surjection
-- statement:
--   Let $X$, $Y$, $Z$ be schemes (in a fixed universe) and let $f : X \to Y$ and $g : Y \to Z$ be morphisms of schemes. Assume that $f$ is smooth, surjective and quasi-compact, and that the composite $f$ followed by $g$, that is $g \circ f : X \to Z$, is smooth. Then $g$ is smooth. All four hypotheses on the morphisms are typeclass assumptions in the Mathlib hierarchy of morphism properties (`Smooth`, `Surjective`, `QuasiCompact`), and the conclusion is the corresponding instance `Smooth g`; no further finiteness assumption on $g$ is imposed, in particular local finite presentation of $g$ is part of the conclusion rather than of the hypotheses.
--
--   This is the descent of smoothness along a quasi-compact smooth surjection on the source, as in EGA IV 17.7.7: smoothness is local on the source for the fppf topology. It is used in the proof of [`AlgebraicGeometry.SmoothOfRelativeDimension.of_comp_of_surjective_of_field`](thm.html#AlgebraicGeometry.SmoothOfRelativeDimension.of_comp_of_surjective_of_field), which supplies relative-dimension bookkeeping for smooth morphisms in the geometric part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Smooth_of_comp_of_smooth_of_surjective.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Smooth.of_comp_of_smooth_of_surjective
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [Smooth f] [Surjective f] [QuasiCompact f]
    [Smooth (f ≫ g)] : Smooth g := by sorry
