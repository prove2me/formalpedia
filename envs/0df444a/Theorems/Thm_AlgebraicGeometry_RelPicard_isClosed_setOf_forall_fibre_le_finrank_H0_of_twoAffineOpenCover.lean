-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_isClosed_setOf_forall_fibre_le_finrank_H0_of_twoAffineOpenCover
-- name    : AlgebraicGeometry.RelPicard.isClosed_setOf_forall_fibre_le_finrank_H0_of_twoAffineOpenCover
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/a1749968-4157-524e-a6d2-b69aef231ea6
-- title:
--   Closedness of the locus where fibrewise h⁰ is at least n
-- statement:
--   Let $R$ be a Noetherian commutative ring and let $c\colon C\to\operatorname{Spec} R$ be a proper flat morphism of schemes, and suppose given a `TwoAffineOpenCover` $\mathcal V$ of $C$, that is, two affine open subschemes $U_0,U_1$ of $C$ with $U_0\sqcup U_1=\top$ and with $U_0\cap U_1$ affine. Let $t\colon T\to\operatorname{Spec} R$ be locally of finite type, and let $M$ be a sheaf of modules on the fibre product $C\times_{\operatorname{Spec}R}T$ which is invertible in the sense that every point of that scheme has an open neighbourhood $U$ for which the pullback of $M$ along the inclusion $U\hookrightarrow C\times_{\operatorname{Spec}R}T$ is isomorphic to the unit sheaf of modules on $U$. Fix $n\in\mathbb N$. The assertion is that the following subset of the topological space of $T$ is closed: the set of points $x$ such that for every field $k$, every morphism $s\colon\operatorname{Spec} k\to T$ sending the closed point to $x$, and every cover $\mathcal W$ of the fibre $(C\times_{\operatorname{Spec}R}T)\times_T\operatorname{Spec} k$ by two affine opens with affine intersection, one has $n\le\dim_k H^0$, where $H^0$ is computed over $k$ through the structure morphism $\operatorname{pullback.snd}$ of that fibre to $\operatorname{Spec} k$ and the pullback of $M$ to the fibre: it is the kernel of the two-chart Čech differential $(m_0,m_1)\mapsto -m_0|_{W_0\cap W_1}+m_1|_{W_0\cap W_1}$ on $\Gamma(M_s,W_0)\times\Gamma(M_s,W_1)$, i.e. the $k$-space of pairs of sections agreeing on the overlap.
--
--   This is the upper semicontinuity of $h^0$ of the fibres of an invertible module in a proper flat family, stated in the two-chart Čech formulation used throughout the treatment of the relative Picard functor, where the fibrewise $H^0$ is realised as the kernel of the Čech differential for a cover of the fibre by two affine opens with affine overlap. It is used in the analysis of the locus in the base where the fibre of a rigidified line bundle is trivial, in the comparison of the relative Picard functor with its zero cut over the smooth locus.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_isClosed_setOf_forall_fibre_le_finrank_H0_of_twoAffineOpenCover.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

theorem AlgebraicGeometry.RelPicard.isClosed_setOf_forall_fibre_le_finrank_H0_of_twoAffineOpenCover
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [Flat c] (𝒱 : C.TwoAffineOpenCover)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (M : (pullback c t).Modules) (hM : Scheme.Modules.IsInvertible M) (n : ℕ) :
    IsClosed {x : T | ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T),
      s.base (IsLocalRing.closedPoint k) = x →
        ∀ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
          n ≤ Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H0} := by sorry
