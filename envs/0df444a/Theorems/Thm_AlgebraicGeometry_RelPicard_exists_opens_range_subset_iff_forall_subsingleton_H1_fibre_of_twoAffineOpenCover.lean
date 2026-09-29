-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_opens_range_subset_iff_forall_subsingleton_H1_fibre_of_twoAffineOpenCover
-- name    : AlgebraicGeometry.RelPicard.exists_opens_range_subset_iff_forall_subsingleton_H1_fibre_of_twoAffineOpenCover
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/9db39676-368e-523e-b54e-ebe796d38242
-- title:
--   Open locus where fibrewise Čech H¹ vanishes, tested on field points
-- statement:
--   Let $R$ be a Noetherian commutative ring, let $c\colon C\to\operatorname{Spec} R$ be a proper morphism of schemes, and assume $C$ carries a two-affine open cover $\mathcal V$, i.e. two affine opens $U_0,U_1$ with $U_0\sqcup U_1=\top$ and $U_0\sqcap U_1$ affine. Let $t\colon T\to\operatorname{Spec} R$ be locally of finite type and let $M$ be a module on the pullback $C\times_{\operatorname{Spec} R}T$ which is invertible in the sense that every point of that scheme has an open neighbourhood $U$ on which the pullback of $M$ along $U\hookrightarrow C\times_{\operatorname{Spec} R}T$ is isomorphic to the unit sheaf of modules of $U$. Then there exists an open subset $U\subseteq T$ such that for every field $k$ and every morphism $s\colon\operatorname{Spec} k\to T$ the following are equivalent: the range of the underlying map of $s$ is contained in $U$; and for every two-affine open cover $\mathcal W$ of the fibre $\operatorname{pullback}(\operatorname{pullback.snd} c\,t)\,s = (C\times_{\operatorname{Spec} R}T)\times_T\operatorname{Spec} k$, the group $H^1$ of the two-chart Čech data of the pullback $\mathrm{fibreModule}$ of $M$ to that fibre, relative to the structure morphism $\mathrm{fibreAt}$ to $\operatorname{Spec} k$ and the cover $\mathcal W$ — that is, the quotient of the sections over $\mathcal W_0\sqcap\mathcal W_1$ by the image of the Čech differential $(m_0,m_1)\mapsto -r_0(m_0)+r_1(m_1)$ — is a subsingleton. The cover $\mathcal V$ of $C$ occurs only as a hypothesis; the open $U$ and the equivalence are stated without reference to it.
--
--   This is the two-chart-Čech form of the statement that the locus in the base over which the first cohomology of an invertible module vanishes on the fibre is open, and that membership of this locus can be tested by field-valued points; it is the analogue, for the two-chart presentation used throughout, of the semicontinuity results of EGA III. It is used in the construction of an open chart of $T$ on which the relative sub-Picard presheaf is identified with a zero-cut, both in general and in the polarised variant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_opens_range_subset_iff_forall_subsingleton_H1_fibre_of_twoAffineOpenCover.lean

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

theorem AlgebraicGeometry.RelPicard.exists_opens_range_subset_iff_forall_subsingleton_H1_fibre_of_twoAffineOpenCover
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] (𝒱 : C.TwoAffineOpenCover)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (M : (pullback c t).Modules) (hM : Scheme.Modules.IsInvertible M) :
    ∃ U : T.Opens, ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T),
      Set.range ⇑s ⊆ (U : Set T) ↔
        ∀ (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
          Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1 := by sorry
