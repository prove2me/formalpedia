-- Prove2me | Theorems.Thm_AlgebraicGeometry_GeometricallyConnected_descendsAlong_surjective
-- name    : AlgebraicGeometry.GeometricallyConnected.descendsAlong_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/53b58592-022b-5d6a-a996-1a13b787ddc9
-- title:
--   Geometric connectedness descends along surjections
-- statement:
--   For schemes over a fixed universe $u$, the theorem asserts the relation `DescendsAlong` between the morphism property `GeometricallyConnected` and the morphism property `Surjective` on `Scheme.{u}`. Here `GeometricallyConnected` holds for a morphism $f : X \to S$ when for every field $K$, every morphism $\operatorname{Spec} K \to S$ and every cartesian square exhibiting a scheme $Z$ together with maps $Z \to X$ and $Z \to \operatorname{Spec} K$ as the fibre product of $f$ with $\operatorname{Spec} K \to S$, the underlying topological space of $Z$ is connected; `Surjective` is surjectivity on underlying spaces. Unwinding `DescendsAlong`, the conclusion is: given morphisms $f : X \to Z$ and $g : Y \to Z$ of schemes admitting a pullback, with $f$ surjective, if the base change of $g$ along $f$, namely the projection $X \times_Z Y \to X$, is geometrically connected in the above sense, then $g$ itself is geometrically connected. Equivalently, in any cartesian square whose base morphism is surjective, geometric connectedness of the pulled-back morphism implies geometric connectedness of the original one.
--
--   This is the descent of geometric connectedness of fibres along a surjective base change, in the form found in EGA IV 4.5.13. It is used to reduce geometric connectedness of a morphism to a statement after a convenient surjective base change, for instance to a point with algebraically closed or Artinian residue data, as in [`AlgebraicGeometry.geometricallyConnected_of_irreducibleSpace_pullback_of_isAlgClosed`](thm.html#AlgebraicGeometry.geometricallyConnected_of_irreducibleSpace_pullback_of_isAlgClosed) and [`AlgebraicGeometry.geometricallyConnected_of_isConnected_preimage_of_section_of_isArtinianRing`](thm.html#AlgebraicGeometry.geometricallyConnected_of_isConnected_preimage_of_section_of_isArtinianRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_GeometricallyConnected_descendsAlong_surjective.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory MorphismProperty AlgebraicGeometry

theorem AlgebraicGeometry.GeometricallyConnected.descendsAlong_surjective :
    DescendsAlong (@GeometricallyConnected : MorphismProperty Scheme.{u}) @Surjective := by sorry
