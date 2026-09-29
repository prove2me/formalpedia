-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_hom_tensorPow_three_support_zeroSchemeIdeal_eq
-- name    : AlgebraicGeometry.Scheme.Modules.exists_hom_tensorPow_three_support_zeroSchemeIdeal_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/7fdb3d1b-5ac8-5d94-8eec-26398ea2c0a0
-- title:
--   A section of L^{⊗ 3} vanishing on three translates
-- statement:
--   Let $k$ be a field and let $t \colon X \to \operatorname{Spec} k$ be a scheme over $k$ such that the object $\mathrm{Over.mk}\ t$ of the over-category carries a group-object structure and a commutative monoid-object structure; the $k$-points are then the morphisms $x \colon \mathrm{Over.mk}\ (\mathbf 1_{\operatorname{Spec} k}) \to \mathrm{Over.mk}\ t$, which form a group, and for such an $x$ one writes $T_x$ for the underlying $X$-morphism $(\mathbf 1 * (\text{toUnit} \gg x)).\mathrm{left} \colon X \to X$, i.e. translation by $x$. Let $L$ be an $X$-module which is invertible in the sense that every point of $X$ has an open neighbourhood $U$ with $(\iota_U)^* L$ isomorphic to the unit module of $U$, and assume the theorem of the square on $k$-points: for all $k$-points $x, y$ there exists an isomorphism $T_x^* L \otimes T_y^* L \cong T_{xy}^* L \otimes L$. Let $\theta \colon \mathbf 1 \to L$ be a global section and $a, b$ two $k$-points. Then there is a global section $s \colon \mathbf 1 \to L^{\otimes 3} = ((\mathbf 1 \otimes L) \otimes L) \otimes L$ whose zero scheme, namely the infimum of those ideal sheaf data $J$ with $\mathrm{coeffIdeal}(s, U) \le J(U)$ for every affine open $U$, has support, as a subset of $X$, equal to $T_a^{-1}(D) \cup T_b^{-1}(D) \cup T_{(ab)^{-1}}^{-1}(D)$, where $D \subseteq X$ is the support of the zero scheme of $\theta$.
--
--   This is the translate-product construction underlying the classical fact that, for a line bundle satisfying the theorem of the square, $L^{\otimes 3}$ has sections whose zero loci are unions of three translates of a given divisor. It is used in the present development to produce enough sections for a frame on $L^{\otimes 3}$ and thence finiteness of the morphism to projective space attached to a projective presentation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_hom_tensorPow_three_support_zeroSchemeIdeal_eq.lean

import Mathlib
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

open scoped CategoryTheory.MonObj

theorem AlgebraicGeometry.Scheme.Modules.exists_hom_tensorPow_three_support_zeroSchemeIdeal_eq
    (k : Type u) [Field k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k))
    [GrpObj (Over.mk t)] [IsCommMonObj (Over.mk t)]
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (hsq : ∀ x y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t,
      Nonempty (
        (Scheme.Modules.pullback (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ x)).left).obj L ⊗
        (Scheme.Modules.pullback (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ y)).left).obj L ≅
        (Scheme.Modules.pullback (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ (x * y))).left).obj L ⊗
        L))
    (θ : 𝟙_ X.Modules ⟶ L)
    (a b : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t) :
    ∃ s : 𝟙_ X.Modules ⟶ L.tensorPow 3,
      ((Scheme.Modules.zeroSchemeIdeal s).support : Set X) =
        (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ a)).left.base ⁻¹'
            ((Scheme.Modules.zeroSchemeIdeal θ).support : Set X) ∪
          (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ b)).left.base ⁻¹'
            ((Scheme.Modules.zeroSchemeIdeal θ).support : Set X) ∪
          (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ (a * b)⁻¹)).left.base ⁻¹'
            ((Scheme.Modules.zeroSchemeIdeal θ).support : Set X) := by sorry
