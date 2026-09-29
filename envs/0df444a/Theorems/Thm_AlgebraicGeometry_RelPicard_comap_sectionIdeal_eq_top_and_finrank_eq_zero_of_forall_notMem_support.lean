-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_comap_sectionIdeal_eq_top_and_finrank_eq_zero_of_forall_notMem_support
-- name    : AlgebraicGeometry.RelPicard.comap_sectionIdeal_eq_top_and_finrank_eq_zero_of_forall_notMem_support
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/74d48df5-a1a9-595f-a70b-bbc52e6fff91
-- title:
--   Section ideal restricted away from the section is everything
-- statement:
--   Let $R$ be a commutative ring, $C$ a scheme and $c : C \to \operatorname{Spec} R$ a separated morphism, let $\sigma$ be a section of $c$ over $\operatorname{Spec} R$ (a morphism $\operatorname{Spec} R \to C$ whose composite with $c$ is the identity), let $k$ be a field and $t : \operatorname{Spec} k \to \operatorname{Spec} R$ a morphism, and let $J$ be a quasi-coherent ideal sheaf (an `IdealSheafData`) on the fibre product $C_t = C \times_{\operatorname{Spec} R} \operatorname{Spec} k$. Write $\sigma_t =$ `rigSection c t σ` for the induced morphism $\operatorname{Spec} k \to C_t$ determined by $t$ followed by $\sigma$ and the identity of $\operatorname{Spec} k$, and let `sectionIdeal c σ t` be its kernel ideal sheaf. Assume no point in the range of $\sigma_t$ lies in the support of $J$. Then the inverse image of `sectionIdeal c σ t` along the closed immersion $V(J) \hookrightarrow C_t$ equals $\top$; this inverse image is invertible in the sense that around each point some affine basic open carries the ideal as the span of a single non-zero-divisor; the composite of the closed immersion of its zero subscheme with $V(J) \hookrightarrow C_t$ and the projection $C_t \to \operatorname{Spec} k$ is a finite morphism; and at every point $q$ of $\operatorname{Spec} k$ the fibre rank of that composite is $0$.
--
--   This is the degenerate ($r = 0$) input to the multidegree computation for line bundles attached to divisors supported on sections: on a component of the fibre that the section does not meet, the restricted section ideal is the unit ideal and the associated twist is trivial, so the component contributes nothing. It is used in the Euler-characteristic computation [`ModularCurve.DRResolvedModelPackage.eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective`](thm.html#ModularCurve.DRResolvedModelPackage.eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_comap_sectionIdeal_eq_top_and_finrank_eq_zero_of_forall_notMem_support.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicCurve_RelCartier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

theorem AlgebraicGeometry.RelPicard.comap_sectionIdeal_eq_top_and_finrank_eq_zero_of_forall_notMem_support
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (σ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    {k : Type u} [Field k] (t : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (J : (pullback c t).IdealSheafData)
    (hJ : ∀ x ∈ Set.range (rigSection c t σ), x ∉ J.support) :
    (sectionIdeal c σ t).comap J.subschemeι = ⊤ ∧
      ((sectionIdeal c σ t).comap J.subschemeι).IsInvertible ∧
      IsFinite (((sectionIdeal c σ t).comap J.subschemeι).subschemeι ≫ J.subschemeι ≫ pullback.snd c t) ∧
      ∀ q : Spec (CommRingCat.of k),
        (((sectionIdeal c σ t).comap J.subschemeι).subschemeι ≫ J.subschemeι ≫ pullback.snd c t).finrank q = 0 := by sorry
