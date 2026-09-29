-- Prove2me | Theorems.Thm_AlgebraicGeometry_SchemeHomOver_ext_of_forall_point_of_isReduced_of_locallyOfFiniteType
-- name    : AlgebraicGeometry.SchemeHomOver.ext_of_forall_point_of_isReduced_of_locallyOfFiniteType
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/722d7885-a953-5794-a2c9-2bce809b365e
-- title:
--   Morphisms from a reduced finite-type κ-scheme agreeing on κ-points
-- statement:
--   Let $\kappa$ be an algebraically closed field and let $X$, $Y$ be schemes equipped with structure morphisms $g_X : X \to \operatorname{Spec}\kappa$ and $g_Y : Y \to \operatorname{Spec}\kappa$, where $g_X$ is locally of finite type and $X$ is reduced; no separatedness or finiteness hypothesis is imposed on $Y$ or on $g_Y$. Let $\varphi$ and $\psi$ be morphisms of $X$ to $Y$ over $\kappa$, that is, elements of the subtype `SchemeHomOver gX gY` of morphisms $X \to Y$ whose composite with $g_Y$ equals $g_X$. Assume that for every element of `SchemeHomOver (𝟙 (Spec (CommRingCat.of κ))) gX`, i.e. every morphism $x : \operatorname{Spec}\kappa \to X$ with $x$ followed by $g_X$ equal to the identity of $\operatorname{Spec}\kappa$ (a $\kappa$-point of $X$ over the base), one has $\varphi \circ x = \psi \circ x$. Then $\varphi = \psi$ as elements of the subtype, hence in particular the two underlying scheme morphisms $X \to Y$ coincide.
--
--   This is the classical statement that a reduced scheme locally of finite type over an algebraically closed field is determined on $\kappa$-points as a source of morphisms, here in the form valid for an arbitrary, not necessarily separated, target. It is used in the construction and rigidity arguments for group laws and group actions on Jacobians and on fake elliptic curves, where two morphisms are compared pointwise, e.g. by the uniqueness results for relative group laws and for maximal-order actions in the Čerednik–Drinfel'd material.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SchemeHomOver_ext_of_forall_point_of_isReduced_of_locallyOfFiniteType.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra

theorem AlgebraicGeometry.SchemeHomOver.ext_of_forall_point_of_isReduced_of_locallyOfFiniteType
    (κ : Type u) [Field κ] [IsAlgClosed κ] {X Y : Scheme.{u}}
    {gX : X ⟶ Spec (CommRingCat.of κ)} {gY : Y ⟶ Spec (CommRingCat.of κ)}
    [LocallyOfFiniteType gX] [IsReduced X]
    (φ ψ : SchemeHomOver gX gY)
    (h : ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of κ))) gX, x.1 ≫ φ.1 = x.1 ≫ ψ.1) :
    φ = ψ := by sorry
