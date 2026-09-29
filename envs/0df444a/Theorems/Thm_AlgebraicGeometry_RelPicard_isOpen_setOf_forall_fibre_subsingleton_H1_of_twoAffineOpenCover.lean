-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_isOpen_setOf_forall_fibre_subsingleton_H1_of_twoAffineOpenCover
-- name    : AlgebraicGeometry.RelPicard.isOpen_setOf_forall_fibre_subsingleton_H1_of_twoAffineOpenCover
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/6eff52f3-03c9-54db-a860-20eb3424db3b
-- title:
--   Openness of the fibrewise Čech H¹-vanishing locus
-- statement:
--   Let $R$ be a Noetherian commutative ring, let $c \colon C \to \operatorname{Spec} R$ be a proper morphism of schemes, and let $\mathcal V$ be a two-affine open cover of $C$, that is, a pair of affine opens $U_0, U_1 \subseteq C$ with $U_0 \sqcup U_1 = \top$ and $U_0 \sqcap U_1$ affine. Let $t \colon T \to \operatorname{Spec} R$ be locally of finite type, and let $M$ be a module on the fibre product $C \times_{\operatorname{Spec} R} T$ which is invertible in the sense that every point of that scheme has an open neighbourhood $U$ for which the restriction of $M$ along $U \hookrightarrow C \times_{\operatorname{Spec} R} T$ is isomorphic to the unit sheaf of modules on $U$. The assertion is that the following subset of $T$ is open: the set of those $x \in T$ such that for every field $k$ (a type in the ambient universe), every morphism $s \colon \operatorname{Spec} k \to T$ whose underlying map sends the closed point of $\operatorname{Spec} k$ to $x$, and every two-affine open cover $\mathcal W = (W_0, W_1)$ of the fibre $(C \times_{\operatorname{Spec} R} T) \times_T \operatorname{Spec} k$, the first Čech cohomology of the pullback of $M$ to that fibre, computed with respect to $\mathcal W$ and relative to the structure morphism `fibreAt c t s` to $\operatorname{Spec} k$ — namely the quotient of the sections over $W_0 \sqcap W_1$ by the image of the difference map $(m_0, m_1) \mapsto -m_0|_{W_0 \sqcap W_1} + m_1|_{W_0 \sqcap W_1}$ from sections over $W_0$ times sections over $W_1$ — is a subsingleton.
--
--   This is the openness half of the semicontinuity theorem for $H^1$ of an invertible sheaf in a proper family, formulated for two-chart Čech cohomology: the locus in the base over which the fibrewise $H^1$ vanishes is open. It is the version in which the two-affine cover of the fibres is obtained by pulling back a fixed two-affine cover $\mathcal V$ of $C$, and it feeds the characterisation of this locus by open subschemes of $T$ in [`AlgebraicGeometry.RelPicard.exists_opens_range_subset_iff_forall_subsingleton_H1_fibre_of_twoAffineOpenCover`](thm.html#AlgebraicGeometry.RelPicard.exists_opens_range_subset_iff_forall_subsingleton_H1_fibre_of_twoAffineOpenCover), used in the construction of the relative Picard functor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_isOpen_setOf_forall_fibre_subsingleton_H1_of_twoAffineOpenCover.lean

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

theorem AlgebraicGeometry.RelPicard.isOpen_setOf_forall_fibre_subsingleton_H1_of_twoAffineOpenCover
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] (𝒱 : C.TwoAffineOpenCover)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (M : (pullback c t).Modules) (hM : Scheme.Modules.IsInvertible M) :
    IsOpen {x : T | ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T),
      s.base (IsLocalRing.closedPoint k) = x →
        ∀ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
          Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1} := by sorry
