-- Prove2me | Theorems.Thm_AlgebraicGeometry_geometricallyConnected_of_forall_connectedSpace_pullback_of_isAlgClosed
-- name    : AlgebraicGeometry.geometricallyConnected_of_forall_connectedSpace_pullback_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/551a6b59-b243-597b-94d8-b6375b605ac6
-- title:
--   Geometric connectedness from algebraically closed fibres
-- statement:
--   Let $R$ be a commutative ring and let $f : X \to \operatorname{Spec} R$ be a morphism from a scheme $X$ to the spectrum of $R$ (both $X$ and the base ring living in a fixed universe). Assume that for every field $k$ in that universe which is algebraically closed and every ring homomorphism $x : R \to k$, the underlying topological space of the fibre product $X \times_{\operatorname{Spec} R} \operatorname{Spec} k$, formed along $f$ and the morphism $\operatorname{Spec} k \to \operatorname{Spec} R$ induced by $x$, is a connected space — that is, it is nonempty and has no nontrivial decomposition into two disjoint open sets. The conclusion is that $f$ satisfies Mathlib's predicate `GeometricallyConnected`, so the same connectedness holds after base change along the spectrum of an arbitrary field over $R$, not merely an algebraically closed one. Thus the hypothesis, tested only on algebraically closed fields, is upgraded to the full geometric statement.
--
--   This is the standard reduction in the theory of geometrically connected morphisms: connectedness of all geometric fibres over algebraically closed fields suffices for geometric connectedness over arbitrary field-valued points. It serves as the bridge supplying the geometric-connectedness clause in [`AlgebraicGeometry.exists_fg_subalgebra_isPullback_smooth_isProper_geometricallyConnected`](thm.html#AlgebraicGeometry.exists_fg_subalgebra_isPullback_smooth_isProper_geometricallyConnected), where a smooth proper morphism with connected geometric fibres is descended to a finitely generated subalgebra.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_geometricallyConnected_of_forall_connectedSpace_pullback_of_isAlgClosed.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.geometricallyConnected_of_forall_connectedSpace_pullback_of_isAlgClosed
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (h : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : R →+* k),
      ConnectedSpace ↥(pullback f (Spec.map (CommRingCat.ofHom x)))) :
    GeometricallyConnected f := by sorry
