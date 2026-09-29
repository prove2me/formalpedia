-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_isFinite_toProj_of_forall_pullbackSection_eq_zero_iff
-- name    : AlgebraicGeometry.Scheme.Modules.ProjPresentation.isFinite_toProj_of_forall_pullbackSection_eq_zero_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/f1e86d78-e663-55e4-866a-8836646b81e6
-- title:
--   Finiteness of a L^{⊗ 3} Proj presentation
-- statement:
--   Let $k$ be an algebraically closed field, $X$ a scheme and $t\colon X\to\operatorname{Spec} k$ a proper morphism with $X$ integral, and suppose the object $\mathrm{Over.mk}\ t$ of the category of schemes over $\operatorname{Spec} k$ carries a group-object structure which is commutative; $k$-points are morphisms $x\colon \mathrm{Over.mk}\ (\mathbf 1_{\operatorname{Spec} k})\to\mathrm{Over.mk}\ t$ over $\operatorname{Spec} k$, and for such an $x$ the translation $T_x\colon X\to X$ is the underlying morphism of $\mathbf 1 * (\text{toUnit}\circ x)$. Let $L$ be a sheaf of modules on $X$ that is invertible in the sense that every point has an open neighbourhood $U$ with $(\text{pullback }U.\iota)(L)$ isomorphic to the unit module on $U$. Assume the theorem of the square in the form: for all $k$-points $x,y$ there exists an isomorphism $T_x^*L\otimes T_y^*L\cong T_{xy}^*L\otimes L$. Let $\theta\colon \mathbf 1_{X.\mathrm{Modules}}\to L$ be a global section, and assume that any $k$-point $x$ for which, for every $k$-point $z$, the pulled-back section $\text{pullbackSection }z^*\theta$ vanishes if and only if $\text{pullbackSection }(zx)^*\theta$ vanishes, equals $1$. Finally let $N\in\mathbb N$ and let $\mathfrak P$ be a `ProjPresentation` of $L^{\otimes 3}$ (the threefold tensor power $((\mathbf 1\otimes L)\otimes L)\otimes L$) relative to $t$ with $N+1$ indices: a family $\sigma_i\in\Gamma(L^{\otimes 3},\top)$, $i\in\mathrm{Fin}(N+1)$, a morphism $\mathfrak P.\mathrm{toProj}\colon X\to\operatorname{Proj}$ of the homogeneous coordinate ring $k[X_0,\dots,X_N]$ whose composite with the structure map of projective space is $t$, such that on every open $V$ contained in $\mathfrak P.\mathrm{toProj}^{-1}D(X_i)$ the map $g\mapsto g\cdot\sigma_i|_V$ from $\Gamma(X,V)$ to $\Gamma(L^{\otimes 3},V)$ is bijective, and such that on $\mathfrak P.\mathrm{toProj}^{-1}D(X_i)$ the pullback of the ratio $X_j/X_i$ times $\sigma_i$ equals $\sigma_j$. Then $\mathfrak P.\mathrm{toProj}$ is a finite morphism.
--
--   This is the finiteness step in the classical argument that $L^{\otimes 3}$ is ample on a proper commutative group scheme once $L$ satisfies the theorem of the square and the zero set of a section of $L$ has trivial set-theoretic stabiliser (Mumford, Abelian Varieties, §6, Application 1). It is used to produce a finite morphism to projective space attached to the third tensor power of the theta bundle on a Jacobian.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_isFinite_toProj_of_forall_pullbackSection_eq_zero_iff.lean

import Mathlib
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

open scoped CategoryTheory.MonObj

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.isFinite_toProj_of_forall_pullbackSection_eq_zero_iff
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k))
    [IsProper t] [IsIntegral X] [GrpObj (Over.mk t)] [IsCommMonObj (Over.mk t)]
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (hsq : ∀ x y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t,
      Nonempty (
        (Scheme.Modules.pullback (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ x)).left).obj L ⊗
        (Scheme.Modules.pullback (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ y)).left).obj L ≅
        (Scheme.Modules.pullback (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ (x * y))).left).obj L ⊗
        L))
    (θ : 𝟙_ X.Modules ⟶ L)
    (hK : ∀ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t,
      (∀ z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t,
        Scheme.Modules.pullbackSection z.left θ = 0 ↔ Scheme.Modules.pullbackSection (z * x).left θ = 0) →
      x = 1)
    {N : ℕ} (𝔓 : (L.tensorPow 3).ProjPresentation t N) :
    IsFinite 𝔓.toProj := by sorry
