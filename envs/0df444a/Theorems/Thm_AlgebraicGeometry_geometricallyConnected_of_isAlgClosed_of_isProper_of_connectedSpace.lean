-- Prove2me | Theorems.Thm_AlgebraicGeometry_geometricallyConnected_of_isAlgClosed_of_isProper_of_connectedSpace
-- name    : AlgebraicGeometry.geometricallyConnected_of_isAlgClosed_of_isProper_of_connectedSpace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/b51b083a-ff62-5d99-8a2c-485acc5a2f55
-- title:
--   Connected proper schemes over algebraically closed fields are geometrically connected
-- statement:
--   Let $k$ be an algebraically closed field, let $Y$ be a scheme, and let $g : Y \to \operatorname{Spec} k$ be a morphism of schemes which is proper, i.e. which satisfies Mathlib's `IsProper` predicate (separated, finite type, universally closed, quasi-compact); assume further that the underlying topological space of $Y$ is connected, i.e. nonempty and preconnected. The conclusion is `GeometricallyConnected g`: for every field $K$ equipped with a $k$-algebra structure, the base change of $g$ along $\operatorname{Spec}$ of the structure morphism $k \to K$, namely the fibre product $Y \times_{\operatorname{Spec} k} \operatorname{Spec} K$, again has connected underlying space (in particular it is nonempty). All data live in a single universe $u$: $k$, $K$ and $Y$ are of type `Type u`, respectively `Scheme.{u}`.
--
--   This is the standard criterion that a connected scheme proper over an algebraically closed field remains connected after arbitrary field base change (EGA IV, 4.5.13–4.5.14, in the proper case proved through global sections). It is used in the development of polarisations on abelian schemes, where connectedness of fibre products has to survive passage to extensions of the base field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_geometricallyConnected_of_isAlgClosed_of_isProper_of_connectedSpace.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

universe u

theorem AlgebraicGeometry.geometricallyConnected_of_isAlgClosed_of_isProper_of_connectedSpace
    (k : Type u) [Field k] [IsAlgClosed k] {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of k))
    [IsProper g] [ConnectedSpace Y] :
    GeometricallyConnected g := by sorry
