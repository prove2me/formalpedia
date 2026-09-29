-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_subsingleton_H1_iff
-- name    : AlgebraicGeometry.RelPicard.exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_subsingleton_H1_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/1f672b83-dc2d-5f35-abe7-c74e14d1374b
-- title:
--   Fibrewise Čech H⁰-rank and H¹-vanishing under field extension
-- statement:
--   Let $R$ be a commutative ring, let $c : C \to \operatorname{Spec} R$ and $t : T \to \operatorname{Spec} R$ be schemes over $R$, and let $F$ be a module on the scheme $C \times_{\operatorname{Spec} R} T$ which is invertible in the sense that every point has an open neighbourhood $U$ on which the restriction of $F$ is isomorphic to the unit module of the sheaf of rings of $U$. Let $k$ be a field and $s : \operatorname{Spec} k \to T$ a point, let $\mathcal{W}$ be a cover of the fibre $(C \times_{\operatorname{Spec} R} T) \times_T \operatorname{Spec} k$ by two affine opens whose union is everything and whose intersection is affine, and let $K$ be a field extension of $k$, giving the point $\operatorname{Spec} K \to \operatorname{Spec} k \to T$. The assertion is that the fibre over $K$ carries such a two-affine cover $\mathcal{W}'$ for which the two-chart Čech invariants of the pulled-back module agree with those over $k$: the $K$-dimension of $H^0$, the module of pairs of sections over the two charts with equal restriction to the overlap, equals the corresponding $k$-dimension, and the quotient $H^1$ of the overlap sections by the differences of chart sections is trivial for $\mathcal{W}'$ if and only if it is trivial for $\mathcal{W}$.
--
--   This is the statement that the dimension of $H^0$ and the vanishing of $H^1$ of an invertible module on a fibre of $C \times_{\operatorname{Spec} R} T \to T$, computed by a two-chart Čech complex, are insensitive to extending the residue field of the point. It feeds the open-chart results on fibres of the relative Picard construction, where fibrewise hypotheses must be checked after passing to a field extension (for example to an algebraic closure).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_subsingleton_H1_iff.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

theorem AlgebraicGeometry.RelPicard.exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_subsingleton_H1_iff
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (F : (pullback c t).Modules)
    (hF : Scheme.Modules.IsInvertible F)
    {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
    (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover) (K : Type u) [Field K] [Algebra k K] :
    ∃ 𝒲' : (pullback (pullback.snd c t) (Scheme.TwoAffineOpenCover.specMap k K ≫ s)).TwoAffineOpenCover,
      Module.finrank K (𝒲'.sectionsOf (fibreAt c t (Scheme.TwoAffineOpenCover.specMap k K ≫ s)) (fibreModule c t (Scheme.TwoAffineOpenCover.specMap k K ≫ s) F)).H0 =
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s F)).H0 ∧
      (Subsingleton (𝒲'.sectionsOf (fibreAt c t (Scheme.TwoAffineOpenCover.specMap k K ≫ s)) (fibreModule c t (Scheme.TwoAffineOpenCover.specMap k K ≫ s) F)).H1 ↔
        Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s F)).H1) := by sorry
