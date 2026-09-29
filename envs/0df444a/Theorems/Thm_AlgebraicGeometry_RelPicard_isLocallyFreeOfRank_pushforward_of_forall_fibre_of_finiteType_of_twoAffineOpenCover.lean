-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_isLocallyFreeOfRank_pushforward_of_forall_fibre_of_finiteType_of_twoAffineOpenCover
-- name    : AlgebraicGeometry.RelPicard.isLocallyFreeOfRank_pushforward_of_forall_fibre_of_finiteType_of_twoAffineOpenCover
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/b26c0b3e-bd4b-5b26-97e2-a55abd250cd6
-- title:
--   Fibrewise h¹=0, h⁰=n gives locally free pushforward
-- statement:
--   Let $R$ be a Noetherian commutative ring, $C$ a scheme and $c : C \to \operatorname{Spec} R$ a proper flat morphism, and let $\mathcal V$ be a two-affine open cover of $C$, that is, a pair of affine opens $U_0, U_1$ with $U_0 \sqcup U_1 = \top$ and $U_0 \sqcap U_1$ affine. Let $A$ be an $R$-algebra of finite type, and let $F$ be a module on the fibre product $C \times_{\operatorname{Spec} R} \operatorname{Spec} A$ which is invertible in the sense that every point has an open neighbourhood $U$ on which the pullback of $F$ along $U \hookrightarrow C_A$ is isomorphic to the unit sheaf of modules on $U$. Let $n$ be a natural number, and assume: for every field $k$, every morphism $s : \operatorname{Spec} k \to \operatorname{Spec} A$ and every two-affine open cover $\mathcal W$ of the fibre $(C_A) \times_{\operatorname{Spec} A} \operatorname{Spec} k$, the two-chart Čech data of the pullback of $F$ to that fibre relative to $\mathcal W$ and to the fibre's structure morphism to $\operatorname{Spec} k$ have $H^1 = 0$ (the quotient of $\Gamma(\mathcal W_0 \sqcap \mathcal W_1)$ by the image of the difference of the two restrictions is a subsingleton) and $\dim_k H^0 = n$, where $H^0$ is the kernel of that difference map on $\Gamma(\mathcal W_0) \times \Gamma(\mathcal W_1)$. Then the pushforward of $F$ along the projection $C_A \to \operatorname{Spec} A$ is locally free of rank $n$: every point of $\operatorname{Spec} A$ has an open neighbourhood on which this module pulls back to the free sheaf of modules on a type with $n$ elements.
--
--   This is the cohomology-and-base-change criterion in the form used for the relative Picard functor: constancy of $h^0$ and vanishing of $h^1$ on all field-valued fibres forces the direct image of an invertible module to be locally free of the expected rank. It is the finite-type-base version of the criterion, stated for a proper flat family equipped with a two-affine open cover, and is used in turn to obtain the corresponding statement over a general affine base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_isLocallyFreeOfRank_pushforward_of_forall_fibre_of_finiteType_of_twoAffineOpenCover.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra MonoidalCategory

theorem AlgebraicGeometry.RelPicard.isLocallyFreeOfRank_pushforward_of_forall_fibre_of_finiteType_of_twoAffineOpenCover
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [Flat c] (𝒱 : C.TwoAffineOpenCover)
    (A : Type u) [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    (F : (pullback c (Spec.map (CommRingCat.ofHom (algebraMap R A)))).Modules)
    (hF : Scheme.Modules.IsInvertible F) (n : ℕ)
    (hfib : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A))
      (𝒲 : (pullback (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap R A)))) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c (Spec.map (CommRingCat.ofHom (algebraMap R A))) s)
        (fibreModule c (Spec.map (CommRingCat.ofHom (algebraMap R A))) s F)).H1 ∧
        Module.finrank k (𝒲.sectionsOf (fibreAt c (Spec.map (CommRingCat.ofHom (algebraMap R A))) s)
          (fibreModule c (Spec.map (CommRingCat.ofHom (algebraMap R A))) s F)).H0 = n) :
    Scheme.Modules.IsLocallyFreeOfRank n
      ((Scheme.Modules.pushforward (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap R A))))).obj F) := by sorry
