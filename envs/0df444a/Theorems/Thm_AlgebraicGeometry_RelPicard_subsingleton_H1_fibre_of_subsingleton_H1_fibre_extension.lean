-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_subsingleton_H1_fibre_of_subsingleton_H1_fibre_extension
-- name    : AlgebraicGeometry.RelPicard.subsingleton_H1_fibre_of_subsingleton_H1_fibre_extension
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/f46a9a70-e8aa-5f5b-810f-2ee90ba2f008
-- title:
--   Vanishing of fibre two-chart H¹ descends along extensions of the residue field
-- statement:
--   Let $R$ be a commutative ring, let $c : C \to \operatorname{Spec} R$ be a separated morphism of schemes, let $t : T \to \operatorname{Spec} R$ be arbitrary, and let $M$ be a sheaf of modules on the pullback $C \times_{\operatorname{Spec} R} T$ which is invertible in the sense that every point has an open neighbourhood $U$ on which the restriction of $M$ is isomorphic to the unit module sheaf of $U$. Let $k$ be a field, $s : \operatorname{Spec} k \to T$ a point of $T$, and $K$ a field extension of $k$, with $s_K$ the composite of $\operatorname{Spec}$ of $k \to K$ with $s$. For a field-valued point of $T$, the fibre is the scheme $\operatorname{pullback}(\mathrm{pr}_2 : C \times_R T \to T, \cdot)$ with its structure morphism `fibreAt` to the spectrum of the field, and the fibre module is the pullback of $M$ along the first projection. Assume that for every two-affine open cover $\mathcal W'$ of the fibre at $s_K$ — that is, every pair of affine opens with affine intersection whose union is everything — the two-chart Čech group $H^1$ of the fibre module at $s_K$, namely the quotient of the sections over $\mathcal W'_0 \cap \mathcal W'_1$ by the image of the difference of the two restriction maps, is a subsingleton. Then the same holds for every two-affine open cover $\mathcal W$ of the fibre at $s$ and the fibre module at $s$.
--
--   This is the descent direction of the comparison of two-chart Čech cohomology of an invertible module on a fibre under enlarging the field of the base point: vanishing of $H^1$ after extension of scalars forces vanishing before. It is used in the construction of two-affine charts at an arbitrary field-valued point of $T$, reducing the vanishing clause there to a geometric point above it, and is cited by the chart suppliers [`AlgebraicGeometry.RelPicard.exists_chart_subsingleton_H1_and_support_subset_fibre_of_twoSidedBlocks_of_injective`](thm.html#AlgebraicGeometry.RelPicard.exists_chart_subsingleton_H1_and_support_subset_fibre_of_twoSidedBlocks_of_injective) and [`AlgebraicGeometry.RelPicard.exists_chart_subsingleton_H1_fibre_of_blocks_of_injective`](thm.html#AlgebraicGeometry.RelPicard.exists_chart_subsingleton_H1_fibre_of_blocks_of_injective).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_subsingleton_H1_fibre_of_subsingleton_H1_fibre_extension.lean

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

theorem AlgebraicGeometry.RelPicard.subsingleton_H1_fibre_of_subsingleton_H1_fibre_extension
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : (pullback c t).Modules) (hM : Scheme.Modules.IsInvertible M)
    {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
    (K : Type u) [Field K] [Algebra k K]
    (hK : ∀ 𝒲' : (pullback (pullback.snd c t) (Scheme.TwoAffineOpenCover.specMap k K ≫ s)).TwoAffineOpenCover,
      Subsingleton (𝒲'.sectionsOf (fibreAt c t (Scheme.TwoAffineOpenCover.specMap k K ≫ s))
        (fibreModule c t (Scheme.TwoAffineOpenCover.specMap k K ≫ s) M)).H1) :
    ∀ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1 := by sorry
