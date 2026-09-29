-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_forall_nonempty_pullback_translate_tensor_iso
-- name    : AlgebraicGeometry.Scheme.Modules.forall_nonempty_pullback_translate_tensor_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/d6c957ca-066b-5935-b39f-2ab3b98b337c
-- title:
--   Theorem of the square for line bundles on an abelian variety
-- statement:
--   Let $k$ be an algebraically closed field, let $X$ be a scheme and let $t \colon X \to \operatorname{Spec} k$ be a morphism such that the object $\mathrm{Over.mk}\ t$ of the category of $k$-schemes carries the structure of a group object which is moreover a commutative monoid object, and assume that $t$ is smooth (`Smooth`), proper (`IsProper`) and geometrically connected (`GeometricallyConnected`). Let $L$ be a module over $X$ (an object of `X.Modules`) satisfying `Scheme.Modules.IsInvertible`, i.e. every point of $X$ lies in an open $U$ for which the pullback of $L$ along the inclusion $U \hookrightarrow X$ is isomorphic to the unit module on $U$. Let $x, y$ be two morphisms from $\mathrm{Over.mk}\ (\mathbb{1}_{\operatorname{Spec} k})$, the terminal object of $k$-schemes, to $\mathrm{Over.mk}\ t$, i.e. two $k$-points of $X$. For a $k$-point $z$ write $T_z$ for the underlying scheme morphism $X \to X$ of the product $\mathbb{1} \cdot (\mathrm{toUnit} \circ z)$ formed in the group-object structure, the translation by $z$. The assertion is that the type of isomorphisms $T_x^{*}L \otimes T_y^{*}L \cong T_{xy}^{*}L \otimes L$ in `X.Modules` is nonempty, where $xy$ is the product of $x$ and $y$ as $k$-points.
--
--   This is the theorem of the square for an abelian variety over an algebraically closed field, in the form $T_x^{*}L \otimes T_y^{*}L \cong T_{xy}^{*}L \otimes L$ for rational points $x, y$ and an invertible module $L$. It is used in the construction of invertible sheaves with finitely many sections on abelian schemes, via [`GoodReductionJacobian.AbelianSchemePropertyBundle.exists_isInvertible_finiteBySections`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.exists_isInvertible_finiteBySections).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_forall_nonempty_pullback_translate_tensor_iso.lean

import Mathlib
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

open scoped CategoryTheory.MonObj

theorem AlgebraicGeometry.Scheme.Modules.forall_nonempty_pullback_translate_tensor_iso
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
