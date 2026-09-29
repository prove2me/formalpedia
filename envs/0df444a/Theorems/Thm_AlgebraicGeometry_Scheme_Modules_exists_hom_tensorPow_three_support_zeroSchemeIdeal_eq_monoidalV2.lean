-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_hom_tensorPow_three_support_zeroSchemeIdeal_eq_monoidalV2
-- name    : AlgebraicGeometry.Scheme.Modules.exists_hom_tensorPow_three_support_zeroSchemeIdeal_eq_monoidalV2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/5ac13392-076f-5504-9840-664f97980256
-- title:
--   Theorem of the square: zero loci of L^{⊗ 3} sections
-- statement:
--   Let $k$ be a field and let $t \colon X \to \operatorname{Spec} k$ be a scheme over $k$ such that the object $\mathrm{Over.mk}\ t$ of the category of $k$-schemes carries the structure of a group object whose multiplication is commutative; thus $X$ is a commutative group scheme over $k$. Write, for a $k$-point $x$ of $X$ (a morphism $\mathrm{Over.mk}\ (\mathbf 1_{\operatorname{Spec} k}) \to \mathrm{Over.mk}\ t$), $T_x$ for the underlying $X$-morphism of $\mathbf 1 * (\mathrm{toUnit} \circ x)$, i.e. translation by $x$. Let $L$ be a module on $X$ which is invertible in the sense that each point of $X$ has an open neighbourhood $U$ whose restriction of $L$ (pullback along $U \hookrightarrow X$) is isomorphic to the unit module on $U$. Assume the theorem of the square on $k$-points: for all $k$-points $x,y$ there exists an isomorphism $T_x^* L \otimes T_y^* L \cong T_{xy}^* L \otimes L$. Let $\theta \colon \mathbf 1_{X\text{-Mod}} \to L$ be a global section of $L$, and let $a,b$ be $k$-points of $X$. Then there is a global section $s \colon \mathbf 1_{X\text{-Mod}} \to L^{\otimes 3}$, where $L^{\otimes 3}$ is the threefold tensor power $((\mathbf 1 \otimes L) \otimes L) \otimes L$ formed by `tensorPow`, such that the support of the ideal sheaf datum `zeroSchemeIdeal s` — the infimum of those ideal sheaf data whose ideal on every affine open $U$ contains the span of the coefficients of $s$ on $U$ — equals, as a subset of $X$, the union of the preimages under the underlying maps of $T_a$, $T_b$ and $T_{(ab)^{-1}}$ of the support of `zeroSchemeIdeal θ`.
--
--   This is the standard consequence of the theorem of the square used to show that $L^{\otimes 3}$ has enough sections to separate points: the translated divisors $T_a^{-1}D \cup T_b^{-1}D \cup T_{(ab)^{-1}}^{-1}D$ are cut out by a single section of $L^{\otimes 3}$. It is used in the project to produce frames on $L^{\otimes 3}$ and, through them, finiteness of the associated morphism to a projective presentation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_hom_tensorPow_three_support_zeroSchemeIdeal_eq_monoidalV2.lean

import Mathlib
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroSchemeV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

open scoped CategoryTheory.MonObj

theorem AlgebraicGeometry.Scheme.Modules.exists_hom_tensorPow_three_support_zeroSchemeIdeal_eq_monoidalV2
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
