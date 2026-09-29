-- Prove2me | Theorems.Thm_AlgebraicGeometry_SchemeHomOver_ext_of_forall_point_of_isReduced_of_isAlgClosed
-- name    : AlgebraicGeometry.SchemeHomOver.ext_of_forall_point_of_isReduced_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/ca04e21e-a6cd-5c68-a803-a943505b1a2f
-- title:
--   Maps from a reduced finite-type scheme agreeing on all κ-points
-- statement:
--   Let $\kappa$ be an algebraically closed field and let $X$, $Y$ be schemes equipped with structure morphisms $g_X : X \to \operatorname{Spec}\kappa$ and $g_Y : Y \to \operatorname{Spec}\kappa$, where $g_X$ is locally of finite type, $X$ is reduced and $g_Y$ is separated. Consider two morphisms over the base, i.e. two elements $\varphi, \psi$ of the subtype of morphisms $X \to Y$ whose composite with $g_Y$ equals $g_X$ (`SchemeHomOver gX gY`, written as pairs consisting of a morphism and a proof of this compatibility). Assume that for every $\kappa$-point of $X$, meaning every element of `SchemeHomOver (𝟙 (Spec (CommRingCat.of κ))) gX`, that is every morphism $x : \operatorname{Spec}\kappa \to X$ with $x$ followed by $g_X$ equal to the identity of $\operatorname{Spec}\kappa$, the two composites $x$ followed by $\varphi$ and $x$ followed by $\psi$ agree as morphisms $\operatorname{Spec}\kappa \to Y$. Then $\varphi = \psi$ as elements of that subtype, in particular the underlying morphisms $X \to Y$ coincide.
--
--   This is the classical rigidity statement that two morphisms of $\kappa$-schemes out of a reduced scheme locally of finite type into a separated $\kappa$-scheme are determined by their values on $\kappa$-rational points, $\kappa$ being algebraically closed. It is used in the Néron-model infrastructure for modular curves, in the verification of the relation between the Frobenius, the Hecke operator $U$ and a diamond operator on fibres of the relevant Néron object.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SchemeHomOver_ext_of_forall_point_of_isReduced_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra

theorem AlgebraicGeometry.SchemeHomOver.ext_of_forall_point_of_isReduced_of_isAlgClosed
    (κ : Type u) [Field κ] [IsAlgClosed κ] {X Y : Scheme.{u}}
    {gX : X ⟶ Spec (CommRingCat.of κ)} {gY : Y ⟶ Spec (CommRingCat.of κ)}
    [LocallyOfFiniteType gX] [IsReduced X] [IsSeparated gY]
    (φ ψ : SchemeHomOver gX gY)
    (h : ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of κ))) gX, x.1 ≫ φ.1 = x.1 ≫ ψ.1) :
    φ = ψ := by sorry
