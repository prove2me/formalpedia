-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_isOpen_setOf_forall_fibre_subsingleton_H1
-- name    : AlgebraicGeometry.RelPicard.isOpen_setOf_forall_fibre_subsingleton_H1
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/59a821a0-6831-5b2c-b8a3-f9beefd38c16
-- title:
--   Openness of the locus of fibrewise vanishing H¹
-- statement:
--   Let $R$ be a Noetherian commutative ring, $c : C \to \operatorname{Spec} R$ a proper morphism that is smooth of relative dimension $1$, and $\varepsilon$ a section of $c$ (a morphism $\operatorname{Spec} R \to C$ composing with $c$ to the identity). Assume `h𝔉`: for every $m_0 \in \mathbb{N}$ there is a `FiniteMapData` for $c$ and $\varepsilon$ of degree $\mathfrak{F}.m \ge m_0$, i.e. two affine opens $U, V$ covering $C$ with $U$ the complement of the image of $\varepsilon$, sections $f \in \Gamma(C,U)$, $g \in \Gamma(C,V)$ whose basic opens both equal $U \cap V$ and whose restrictions are mutually inverse there, making $\Gamma(C,U)$ and $\Gamma(C,V)$ finite over $R[x]$ via $f$, resp. $g$, and such that for every local $R$-algebra $S$ and every $s \in S$ the level set $S \otimes_R \Gamma(C,U)/(1\otimes f - s \otimes 1)$ is finite free of rank $\mathfrak{F}.m$. Let $t : T \to \operatorname{Spec} R$ be locally of finite type and let $M$ be a module on $C \times_{\operatorname{Spec} R} T$ that is invertible, in the sense that every point has an open neighbourhood on which $M$ restricts to a module isomorphic to the unit sheaf of modules. Then the following subset of $T$ is open: the set of $x$ such that for every field $k$, every $s : \operatorname{Spec} k \to T$ carrying the closed point of $\operatorname{Spec} k$ to $x$, and every cover $\mathcal{W}$ of the fibre $(C \times_{\operatorname{Spec} R} T) \times_T \operatorname{Spec} k$ by two affine opens with affine intersection, the two-chart Čech $H^1$ of the sections of the pulled-back module `fibreModule c t s M` relative to the structure morphism `fibreAt c t s` — the quotient of the sections over $\mathcal{W}.U_0 \cap \mathcal{W}.U_1$ by the image of the difference of the two restriction maps — is a subsingleton.
--
--   This is the openness (upper semicontinuity) of the locus in the base where the first cohomology of an invertible module vanishes on the geometric fibres of a relative smooth proper curve, phrased in the pointwise fibre-by-fibre two-chart Čech form used throughout the construction of the relative Picard scheme and the Jacobian. It is cited by [`AlgebraicGeometry.RelPicard.exists_opens_range_subset_iff_forall_subsingleton_H1_fibre`](thm.html#AlgebraicGeometry.RelPicard.exists_opens_range_subset_iff_forall_subsingleton_H1_fibre), which converts the locus into an honest open subscheme of $T$ over which the pushforward statements for line bundles are available.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_isOpen_setOf_forall_fibre_subsingleton_H1.lean

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

theorem AlgebraicGeometry.RelPicard.isOpen_setOf_forall_fibre_subsingleton_H1
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (M : (pullback c t).Modules) (hM : Scheme.Modules.IsInvertible M) :
    IsOpen {x : T | ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T),
      s.base (IsLocalRing.closedPoint k) = x →
        ∀ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
          Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1} := by sorry
