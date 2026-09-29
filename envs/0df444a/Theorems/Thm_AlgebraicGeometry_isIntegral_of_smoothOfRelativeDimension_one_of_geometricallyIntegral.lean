-- Prove2me | Theorems.Thm_AlgebraicGeometry_isIntegral_of_smoothOfRelativeDimension_one_of_geometricallyIntegral
-- name    : AlgebraicGeometry.isIntegral_of_smoothOfRelativeDimension_one_of_geometricallyIntegral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/9b20dc68-494b-55cd-8643-bd9681b82427
-- title:
--   Integrality of a geometrically integral smooth proper curve
-- statement:
--   Let $k$ be a field and let $C$ be a scheme, both in the lowest universe, and let $c : C \to \operatorname{Spec} k$ be a morphism of schemes to the spectrum of $k$ (viewed as a commutative ring object). Assume that $c$ is proper in the sense of Mathlib's `IsProper`, that it is smooth of relative dimension $1$, i.e. satisfies `SmoothOfRelativeDimension 1`, and that it satisfies the predicate `GeometricallyIntegral`, the project's notion expressing integrality of $C$ over $k$ after geometric base change. The conclusion is that the scheme $C$ is itself integral, i.e. `IsIntegral C` holds: its underlying topological space is irreducible and nonempty and its structure sheaf has no nonzero nilpotents, in the formulation of Mathlib's `IsIntegral` for schemes. Thus the assertion is the descent of integrality from the geometric situation to $C$ itself, in the presence of the properness and relative-dimension-one smoothness hypotheses on $c$.
--
--   This is the standard fact that a geometrically integral curve over a field is an integral scheme, stated in the form needed for smooth proper curves over a field. It serves as an input wherever an integral curve is required, in particular for the components of the special fibre of the modular curve $X_1(p)$ and the existence of their Jacobians.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isIntegral_of_smoothOfRelativeDimension_one_of_geometricallyIntegral.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve

theorem AlgebraicGeometry.isIntegral_of_smoothOfRelativeDimension_one_of_geometricallyIntegral
    {k : Type} [Field k] {C : Scheme.{0}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c] : IsIntegral C := by sorry
