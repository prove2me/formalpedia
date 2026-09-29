-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_isFinite_toProj_of_finite_setOf_forall_pullbackSection_eq_zero_iff
-- name    : AlgebraicGeometry.Scheme.Modules.ProjPresentation.isFinite_toProj_of_finite_setOf_forall_pullbackSection_eq_zero_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/ca8090eb-9dc5-55f5-9d31-9e959bcd63e6
-- title:
--   Finiteness of the morphism defined by L^{⊗ 3}
-- statement:
--   Let $k$ be an algebraically closed field, let $X$ be a scheme and $t : X \to \operatorname{Spec} k$ a proper morphism, let $X$ be integral, and let the object $\mathrm{Over.mk}\ t$ of the category of $k$-schemes carry the structure of a group object which is moreover a commutative monoid object; write a "$k$-point" for a morphism $\mathrm{Over.mk}\,(\mathbf 1_{\operatorname{Spec} k}) \to \mathrm{Over.mk}\ t$ over $\operatorname{Spec} k$, and for such a point $x$ let $T_x$ be the morphism $X \to X$ underlying $\mathbf 1 * (\text{toUnit} \circ x)$, i.e. translation by $x$. Let $L$ be a module on $X$ which is invertible in the sense that every point of $X$ has an open neighbourhood $U$ with $(\text{pullback along } U \hookrightarrow X)(L)$ isomorphic to the unit module on $U$; assume the theorem of the square in the form that for all $k$-points $x,y$ there is an isomorphism $T_x^*L \otimes T_y^*L \cong T_{xy}^*L \otimes L$. Let $\theta : \mathbf 1_{X.\mathrm{Modules}} \to L$ be a global section, and assume the set of $k$-points $x$ such that for every $k$-point $z$ the pullback of $\theta$ along $z$ vanishes if and only if the pullback of $\theta$ along $z \cdot x$ vanishes, is finite. Let $N \in \mathbb N$ and let $\mathfrak P$ be a `ProjPresentation` of $L^{\otimes 3}$ (the threefold tensor power $((\mathbf 1 \otimes L) \otimes L) \otimes L$) over $t$ with $N+1$ sections: that is, global sections $\sigma_0,\dots,\sigma_N$ of $L^{\otimes 3}$ together with a morphism $\mathfrak P.\mathrm{toProj} : X \to \operatorname{Proj} k[X_0,\dots,X_N]$ composing with the structure morphism of projective space to give $t$, such that on every open $V$ contained in the preimage of the basic open $D(X_i)$ multiplication by the restriction of $\sigma_i$ is a bijection $\Gamma(X,V) \to \Gamma(L^{\otimes 3},V)$, and such that the pullback of the ratio $X_j/X_i$ carries $\sigma_i$ to $\sigma_j$ over the preimage of $D(X_i)$. Then $\mathfrak P.\mathrm{toProj}$ is a finite morphism.
--
--   This is Application 1 of §6 of Mumford's treatment of abelian varieties, in the generality of a finite (rather than trivial) set-theoretic stabiliser of the zero set of $\theta$: a line bundle satisfying the theorem of the square whose section has finite stabiliser gives, after passing to the third tensor power, a finite morphism to projective space, hence ampleness. It is used in the construction of projective embeddings of abelian schemes, via [`GoodReductionJacobian.AbelianSchemePropertyBundle.exists_isInvertible_finiteBySections`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.exists_isInvertible_finiteBySections).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_isFinite_toProj_of_finite_setOf_forall_pullbackSection_eq_zero_iff.lean

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

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.isFinite_toProj_of_finite_setOf_forall_pullbackSection_eq_zero_iff
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
    (hK : Set.Finite {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t |
        ∀ z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t,
          Scheme.Modules.pullbackSection z.left θ = 0 ↔ Scheme.Modules.pullbackSection (z * x).left θ = 0})
    {N : ℕ} (𝔓 : (L.tensorPow 3).ProjPresentation t N) :
    IsFinite 𝔓.toProj := by sorry
