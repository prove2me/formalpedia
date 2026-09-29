-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback
-- name    : AlgebraicGeometry.RelPicard.exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/ea0e5133-2e26-577b-827c-7a729cd1600d
-- title:
--   Two-chart Čech cohomology transports along any cartesian fibre presentation
-- statement:
--   Let $R$ be a commutative ring, let $c : C \to \operatorname{Spec} R$ and $t : T \to \operatorname{Spec} R$ be morphisms of schemes, and let $M$ be a module on the fibre product $C \times_{\operatorname{Spec} R} T$. Let $k$ be a field, $s : \operatorname{Spec} k \to T$ a $k$-valued point of $T$, and suppose given a scheme $Y$ with morphisms $y : Y \to \operatorname{Spec} k$ and $g' : Y \to C \times_{\operatorname{Spec} R} T$ such that the square formed by $g'$, $y$, the second projection $C \times_{\operatorname{Spec} R} T \to T$ and $s$ is cartesian, i.e. $Y$ is any presentation of the fibre. Let $F$ be a module on $Y$ together with an isomorphism $F \cong (g')^{*}M$, and let $\mathcal{V}$ be a `TwoAffineOpenCover` of $Y$, that is, a pair of affine opens $U_0, U_1$ with $U_0 \sqcup U_1 = \top$ and $U_0 \sqcap U_1$ affine. Then there exists a `TwoAffineOpenCover` $\mathcal{W}$ of the chosen fibre $(C \times_{\operatorname{Spec} R} T) \times_T \operatorname{Spec} k$ such that both the degree-zero and the degree-one groups of the two-chart Čech complex agree: writing `sectionsOf` for the triple $\bigl(\Gamma(F, U_0), \Gamma(F, U_1), \Gamma(F, U_0 \sqcap U_1)\bigr)$ with the two restriction maps, and $H^0$ for the kernel and $H^1$ for the cokernel of the difference map $(m_0, m_1) \mapsto r_1 m_1 - r_0 m_0$, there are $k$-linear isomorphisms (asserted as nonemptiness) between the $H^0$, respectively $H^1$, of $\mathcal{V}$ with $F$ over $y$ and those of $\mathcal{W}$ with the pulled-back module `fibreModule c t s M` over the structural morphism `fibreAt c t s` to $\operatorname{Spec} k$.
--
--   This is a transport-of-structure statement: it lets a hypothesis or computation about the two-chart Čech cohomology of the canonical fibre $(C \times_{\operatorname{Spec} R} T) \times_T \operatorname{Spec} k$ (such as vanishing of $H^1$ or a dimension count for $H^0$) be read off from any other cartesian presentation $Y \to \operatorname{Spec} k$ of that fibre, together with any module isomorphic to the pullback of $M$. It is used in the fibrewise criteria for the relative Picard construction, e.g. in the characterisation of the open locus where all fibres have vanishing $H^1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  AlgebraicGeometry.SmoothProperCurve

theorem AlgebraicGeometry.RelPicard.exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : (pullback c t).Modules)
    {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
    {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of k)) (g' : Y ⟶ pullback c t)
    (hcart : IsPullback g' y (pullback.snd c t) s)
    (F : Y.Modules) (e : F ≅ (Scheme.Modules.pullback g').obj M) (𝒱 : Y.TwoAffineOpenCover) :
    ∃ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
      Nonempty ((𝒱.sectionsOf y F).H0 ≃ₗ[k] (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H0) ∧
      Nonempty ((𝒱.sectionsOf y F).H1 ≃ₗ[k] (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1) := by sorry
