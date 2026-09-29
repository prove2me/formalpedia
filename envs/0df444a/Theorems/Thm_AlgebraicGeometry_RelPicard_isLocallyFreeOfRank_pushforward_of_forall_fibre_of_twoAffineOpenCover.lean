-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_isLocallyFreeOfRank_pushforward_of_forall_fibre_of_twoAffineOpenCover
-- name    : AlgebraicGeometry.RelPicard.isLocallyFreeOfRank_pushforward_of_forall_fibre_of_twoAffineOpenCover
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/9aafb517-1494-5d3a-9cca-bb6249c382a5
-- title:
--   Fibrewise h¹=0, h⁰=n gives locally free direct image
-- statement:
--   Let $R$ be a Noetherian commutative ring, let $c\colon C\to\operatorname{Spec}R$ be a proper flat morphism of schemes, and let $\mathcal V$ be a two-affine open cover of $C$, i.e. two affine opens $U_0,U_1$ with $U_0\sqcup U_1=\top$ and $U_0\cap U_1$ affine. Let $t\colon T\to\operatorname{Spec}R$ be locally of finite type, and let $F$ be a module on the fibre product $C\times_{\operatorname{Spec}R}T$ which is invertible in the sense that every point has an open neighbourhood $U$ over which the pullback of $F$ along $U\hookrightarrow C\times_R T$ is isomorphic to the unit sheaf of modules of $U$. Fix $n\in\mathbb N$, and assume the following fibrewise hypothesis: for every field $k$, every morphism $s\colon\operatorname{Spec}k\to T$ and every two-affine open cover $\mathcal W$ of the fibre $(C\times_R T)\times_T\operatorname{Spec}k$, the two-chart Čech complex of the pullback of $F$ to that fibre relative to $\mathcal W$ and to the structural morphism to $\operatorname{Spec}k$ — with terms $\Gamma$ over $W_0$, $W_1$, $W_0\cap W_1$ and differential $(m_0,m_1)\mapsto m_1|_{W_0\cap W_1}-m_0|_{W_0\cap W_1}$ — has $H^1$ (the quotient of $\Gamma(W_0\cap W_1)$ by the image of the differential) a subsingleton, and $H^0$ (the kernel of the differential) of $k$-dimension $n$. Then the pushforward of $F$ along the projection $\operatorname{pr}_2\colon C\times_R T\to T$ is locally free of rank $n$: every point of $T$ has an open neighbourhood $U$ such that the restriction of this pushforward to $U$ is isomorphic to the free module of rank $n$.
--
--   This is the cohomology-and-base-change criterion for local freeness of a direct image (constancy of $h^0$ together with vanishing of $h^1$ on all field-valued fibres), here in the form where fibre cohomology is computed by two-chart Čech complexes and the base $T$ is only assumed locally of finite type over $R$. It supplies the local-freeness input to the construction of the relative Picard scheme and its zero-cut description, being used in the representability statements for relative sub-Picard functors over smooth loci of curve and line degenerations, and in the comparison of open subschemes with supports of zero-scheme ideals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_isLocallyFreeOfRank_pushforward_of_forall_fibre_of_twoAffineOpenCover.lean

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

theorem AlgebraicGeometry.RelPicard.isLocallyFreeOfRank_pushforward_of_forall_fibre_of_twoAffineOpenCover
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [Flat c] (𝒱 : C.TwoAffineOpenCover)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (F : (pullback c t).Modules) (hF : Scheme.Modules.IsInvertible F) (n : ℕ)
    (hfib : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
      (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s F)).H1 ∧
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s F)).H0 = n) :
    Scheme.Modules.IsLocallyFreeOfRank n ((Scheme.Modules.pushforward (pullback.snd c t)).obj F) := by sorry
