-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_fibreIso_hom_comp_eq
-- name    : AlgebraicGeometry.RelPicard.exists_fibreIso_hom_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/2e3e59d4-80e6-513a-b40c-de80738d5b97
-- title:
--   Fibre of a base change is the fibre, compatibly
-- statement:
--   Let $R$ be a commutative ring, let $c \colon C \to \operatorname{Spec} R$ and $t \colon T \to \operatorname{Spec} R$ be morphisms of schemes, let $k$ be a field, and let $s \colon \operatorname{Spec} k \to T$ and $x \colon \operatorname{Spec} k \to \operatorname{Spec} R$ be morphisms with $s$ followed by $t$ equal to $x$. The assertion is that there exists an isomorphism of schemes
--   $$\varphi \colon (C \times_{\operatorname{Spec} R} T) \times_T \operatorname{Spec} k \;\xrightarrow{\ \sim\ }\; C \times_{\operatorname{Spec} R, x} \operatorname{Spec} k$$
--   satisfying three compatibilities: first, $\varphi$ followed by the second projection of $C \times_{\operatorname{Spec} R} \operatorname{Spec} k$ equals `fibreAt c t s`, i.e. the second projection of the iterated pullback $(C \times_{\operatorname{Spec} R} T) \times_T \operatorname{Spec} k \to \operatorname{Spec} k$; second, $\varphi$ followed by the first projection to $C$ equals the first projection of the iterated pullback followed by the first projection $C \times_{\operatorname{Spec} R} T \to C$; and third, $\varphi$ followed by `baseChangeSnd c ⟨s, hx⟩`, the morphism $C \times_{\operatorname{Spec} R} \operatorname{Spec} k \to C \times_{\operatorname{Spec} R} T$ obtained from the identity of $C$ and from $s$ viewed as a morphism over $\operatorname{Spec} R$, equals the first projection of the iterated pullback.
--
--   This is the pasting (transitivity) of fibre products in the form "the fibre of a base change is the fibre", recorded together with the three compatibilities needed to transport data along it. It is used where fibrewise hypotheses for the relative Picard functor are formulated on the iterated fibre $(C \times_{\operatorname{Spec} R} T) \times_T \operatorname{Spec} k$ while statements about a single geometric fibre of $c$ are formulated on $C \times_{\operatorname{Spec} R} \operatorname{Spec} k$, for instance in the results producing charts on which Čech $H^1$ is subsingleton.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_fibreIso_hom_comp_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
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

theorem AlgebraicGeometry.RelPicard.exists_fibreIso_hom_comp_eq
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T) (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (hx : s ≫ t = x) :
    ∃ φ : pullback (pullback.snd c t) s ≅ pullback c x,
      φ.hom ≫ pullback.snd c x = fibreAt c t s ∧
      φ.hom ≫ pullback.fst c x = pullback.fst (pullback.snd c t) s ≫ pullback.fst c t ∧
      φ.hom ≫ baseChangeSnd c (⟨s, hx⟩ : SchemeHomOver x t) = pullback.fst (pullback.snd c t) s := by sorry
