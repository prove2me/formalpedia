-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_isFinite_toProj_of_finite_setOf_forall_pullbackSection_eq_zero_iff_monoidalV2
-- name    : AlgebraicGeometry.Scheme.Modules.ProjPresentation.isFinite_toProj_of_finite_setOf_forall_pullbackSection_eq_zero_iff_monoidalV2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/3cd353e5-c968-598f-a5c8-49149dd1b1ec
-- title:
--   Finiteness of the map defined by L^{⊗ 3}
-- statement:
--   Let $k$ be an algebraically closed field, let $X$ be an integral scheme with a proper morphism $t \colon X \to \operatorname{Spec} k$, and suppose the object $X$ over $\operatorname{Spec} k$ carries a group-object structure whose underlying monoid object is commutative; points of $X$ valued in $k$ are understood as morphisms $\operatorname{Spec} k \to X$ over $\operatorname{Spec} k$, and for such a point $x$ the associated translation is the left component of $\mathbb{1} * (\text{toUnit} \gg x)$. Let $L$ be a sheaf of modules on $X$ which is invertible in the sense that every point of $X$ has an open neighbourhood $U$ with the pullback of $L$ along $U \hookrightarrow X$ isomorphic to the unit module sheaf of $U$, and assume the theorem of the square: for all $k$-points $x, y$ there is an isomorphism between the tensor product of the pullbacks of $L$ along the translations by $x$ and by $y$ and the tensor product of the pullback of $L$ along the translation by $xy$ with $L$. Let $\theta \colon \mathbb{1} \to L$ be a global section, and for a $k$-point $z$ write $z^{*}\theta$ for the induced section `Scheme.Modules.pullbackSection z.left θ` of the pullback of $L$ to $\operatorname{Spec} k$, obtained from the inverse of the canonical isomorphism identifying the pullback of the unit with the unit followed by the pullback of $\theta$. Assume the set of $k$-points $x$ such that for every $k$-point $z$ one has $z^{*}\theta = 0$ if and only if $(zx)^{*}\theta = 0$ is finite. Finally let $N$ be a natural number and let $\mathfrak{P}$ be a `ProjPresentation` of $L^{\otimes 3} = ((\mathbb{1} \otimes L) \otimes L) \otimes L$ relative to $t$ with $N+1$ sections, that is: sections $\sigma_0, \dots, \sigma_N$ of $L^{\otimes 3}$ over $X$, a morphism $\mathfrak{P}.\mathrm{toProj} \colon X \to \operatorname{Proj}$ of the polynomial ring in $N+1$ variables over $k$ with its standard grading, compatible with $t$ via the structure morphism of projective space, such that on any open $V$ contained in the preimage of the basic open set of $X_i$ multiplication by a function on $V$ against the restriction of $\sigma_i$ is a bijection onto the sections of $L^{\otimes 3}$ over $V$, and such that the ratios $X_j/X_i$ pulled back along $\mathfrak{P}.\mathrm{toProj}$ carry $\sigma_i$ to $\sigma_j$ over the preimage of the basic open set of $X_i$. Then the morphism $\mathfrak{P}.\mathrm{toProj}$ is finite.
--
--   This is Application 1 of §6 of Mumford's theory of abelian varieties, in the generality where only the set-theoretic stabiliser of the zero set of $\theta$ is assumed finite rather than trivial: a morphism to projective space presented by global sections of $L^{\otimes 3}$ is finite. It is used in the construction of polarisations, namely in [`AlgebraicGeometry.Polarisation.finiteBySections_of_iso_tensorPow_three_of_finite_kernelPts_of_finrank_pos`](thm.html#AlgebraicGeometry.Polarisation.finiteBySections_of_iso_tensorPow_three_of_finite_kernelPts_of_finrank_pos).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_isFinite_toProj_of_finite_setOf_forall_pullbackSection_eq_zero_iff_monoidalV2.lean

import Mathlib
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroSchemeV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

open scoped CategoryTheory.MonObj

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.isFinite_toProj_of_finite_setOf_forall_pullbackSection_eq_zero_iff_monoidalV2
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
