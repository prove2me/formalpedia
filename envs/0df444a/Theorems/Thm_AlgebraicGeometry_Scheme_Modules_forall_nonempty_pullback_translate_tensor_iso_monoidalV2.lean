-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_forall_nonempty_pullback_translate_tensor_iso_monoidalV2
-- name    : AlgebraicGeometry.Scheme.Modules.forall_nonempty_pullback_translate_tensor_iso_monoidalV2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/ea9159f5-2e45-5be3-9500-de5876990536
-- title:
--   Theorem of the square for translations of an invertible sheaf
-- statement:
--   Let $k$ be an algebraically closed field and let $t \colon X \to \operatorname{Spec} k$ be a morphism of schemes such that the object $\mathrm{Over.mk}\ t$ of the category of schemes over $\operatorname{Spec} k$ carries a group-object structure whose multiplication is commutative, and such that $t$ is smooth, proper and geometrically connected. Let $L$ be an $\mathcal{O}_X$-module (an object of `X.Modules`) which is invertible in the sense of `Scheme.Modules.IsInvertible`: every point of $X$ has an open neighbourhood $U$ on which the pullback of $L$ along the inclusion $U \hookrightarrow X$ is isomorphic to the unit module over the sheaf of rings of $U$. Let $x, y$ be two $k$-points, that is, morphisms from $\mathrm{Over.mk}\ (\mathbf{1}_{\operatorname{Spec} k})$ to $\mathrm{Over.mk}\ t$ over $\operatorname{Spec} k$. For a $k$-point $z$ write $T_z$ for the underlying morphism $X \to X$ of the product, in the group object $\mathrm{Over.mk}\ t$, of the identity with the composite of the terminal map $\mathrm{Over.mk}\ t \to \mathrm{Over.mk}\ (\mathbf{1}_{\operatorname{Spec} k})$ followed by $z$, i.e. translation by $z$. The conclusion is that the type of isomorphisms $T_x^{*}L \otimes T_y^{*}L \cong T_{xy}^{*}L \otimes L$ in `X.Modules` is nonempty, where $xy$ is the product of $x$ and $y$ under the group law and the tensor products are those of the monoidal structure on `X.Modules`.
--
--   This is the theorem of the square for an invertible sheaf on an abelian variety over an algebraically closed field, obtained from the pullback form of the theorem of the cube together with the triviality of invertible sheaves on $\operatorname{Spec} k$. It is used in the construction and study of polarisations, for instance in the results on frames and on sections of $L \otimes L$ and of tensor products of translates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_forall_nonempty_pullback_translate_tensor_iso_monoidalV2.lean

import Mathlib
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

open scoped CategoryTheory.MonObj

theorem AlgebraicGeometry.Scheme.Modules.forall_nonempty_pullback_translate_tensor_iso_monoidalV2
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k))
    [GrpObj (Over.mk t)] [IsCommMonObj (Over.mk t)]
    (hsm : Smooth t) (hpr : IsProper t) (hgc : GeometricallyConnected t)
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (x y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t) :
    Nonempty (
      (Scheme.Modules.pullback (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ x)).left).obj L ⊗
      (Scheme.Modules.pullback (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ y)).left).obj L ≅
      (Scheme.Modules.pullback (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ (x * y))).left).obj L ⊗
      L) := by sorry
