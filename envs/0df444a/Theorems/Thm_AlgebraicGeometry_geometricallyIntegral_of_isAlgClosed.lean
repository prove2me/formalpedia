-- Prove2me | Theorems.Thm_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed
-- name    : AlgebraicGeometry.geometricallyIntegral_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/eca317a3-987b-54b5-a521-c23bef271d33
-- title:
--   Integral finite-type schemes over an algebraically closed field are geometrically integral
-- statement:
--   Let $K$ be an algebraically closed field (in a fixed universe) and let $X$ be a scheme in the same universe, equipped with a morphism $f \colon X \to \operatorname{Spec} K$, where $\operatorname{Spec} K$ is the spectrum of $K$ viewed as a commutative ring object. Assume that $X$ is an integral scheme, i.e. nonempty, reduced and irreducible, and that $f$ is locally of finite type. The conclusion is that $f$ is geometrically integral: integrality of the source persists after base change along an arbitrary field extension of $K$, so that for every extension field $L$ of $K$ the fibre product $X \times_{\operatorname{Spec} K} \operatorname{Spec} L$ is again an integral scheme. Note that integrality is imposed on $X$ as a scheme, not on the fibres of $f$ separately, and that no properness, separatedness or quasi-compactness hypothesis is made; finite type is assumed only locally, and algebraic closedness of the base is what makes the conclusion hold without further conditions on the function field of $X$.
--
--   This is the standard fact that over an algebraically closed field integrality is a geometric property for schemes locally of finite type, the function field of such an $X$ being a regular extension of $K$; equivalently it encodes the algebraic statement that $A \otimes_K B$ is a domain whenever $A$ is a finitely generated $K$-domain and $B$ any $K$-domain. It is used throughout the geometric part of the development, in particular in the treatment of curves over algebraically closed fields and of relative Picard schemes and Abel–Jacobi maps, where integrality of base changes of a given integral curve is needed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u
open AlgebraicGeometry CategoryTheory

theorem AlgebraicGeometry.geometricallyIntegral_of_isAlgClosed
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) [IsIntegral X] [LocallyOfFiniteType f] :
    GeometricallyIntegral f := by sorry
