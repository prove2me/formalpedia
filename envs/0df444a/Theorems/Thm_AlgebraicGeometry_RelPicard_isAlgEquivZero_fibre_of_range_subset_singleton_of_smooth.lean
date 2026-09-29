-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_isAlgEquivZero_fibre_of_range_subset_singleton_of_smooth
-- name    : AlgebraicGeometry.RelPicard.isAlgEquivZero_fibre_of_range_subset_singleton_of_smooth
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/8518e6d4-6b53-5f33-baa2-069dcd490b6b
-- title:
--   Independence of algebraic equivalence to zero along smooth fibres
-- statement:
--   Let $R$ be a Noetherian commutative ring, $C$ a scheme and $c : C \to \operatorname{Spec} R$ a proper flat morphism; let $\mathcal V$ be a cover of $C$ by two affine opens $U_0, U_1$ with $U_0 \sqcup U_1 = \top$ and $U_0 \cap U_1$ affine. Assume $hH0$: for every $R$-algebra $A$, the structure map $A \to \Gamma(C \times_{\operatorname{Spec} R} \operatorname{Spec} A, \top)$ (the algebra structure coming from the second projection of the base change) is bijective. Let $U \subseteq C$ be an open whose inclusion followed by $c$ is smooth of relative dimension $1$, and let $\varepsilon$ be a section of $c$, i.e. a morphism $\operatorname{Spec} R \to C$ with $\varepsilon \circ$-composite equal to the identity after composing with $c$. Assume $hgoodU$: for every algebraically closed field $k$ and every $x : \operatorname{Spec} k \to \operatorname{Spec} R$ for which $\mathrm{pullback.snd}\ c\ x$ is smooth, the image of the first projection $C \times_{\operatorname{Spec} R} \operatorname{Spec} k \to C$ lies in $U$. The conclusion asserts: for every scheme $T$ with $t : T \to \operatorname{Spec} R$ locally of finite type, every rigidified line bundle $L$ on $C \times_{\operatorname{Spec} R} T$ relative to $\varepsilon$ (an invertible module $L.L$ together with a trivialisation of its pullback along the rigidifying section $\mathrm{rigSection}\ c\ t\ \varepsilon$), every point $x$ of $T$, every algebraically closed field $k_1$ and morphism $s_1 : \operatorname{Spec} k_1 \to T$ whose image on points is contained in $\{x\}$, if the restriction of $L.L$ to the fibre $\bigl(C \times_{\operatorname{Spec} R} T\bigr) \times_T \operatorname{Spec} k_1$ over $\mathrm{fibreAt}\ c\ t\ s_1$ satisfies $\mathrm{IsAlgEquivZero}$ — that is, there exist a scheme $T'$ with a locally of finite type, geometrically integral morphism $h : T' \to \operatorname{Spec} k_1$, an invertible module $M$ on the fibre product of the fibre with $h$, and two sections $t_0, t_1$ of $h$, such that the pullback of $M$ along $t_0$ is isomorphic to the unit module and its pullback along $t_1$ is isomorphic to the given module — then the same property $\mathrm{IsAlgEquivZero}$ holds for any other algebraically closed field $k_2$ and morphism $s_2 : \operatorname{Spec} k_2 \to T$ with image contained in $\{x\}$ for which $\mathrm{pullback.snd}\ c\ (s_2 \circ t)$ is smooth.
--
--   This is the smooth-fibre half of the statement that the condition ‘algebraically equivalent to zero’ on the fibre of a rigidified line bundle at a point of the base does not depend on the choice of geometric point above that point, in the situation of a proper flat curve-like $C/R$ with connected fibres. It is used by [`AlgebraicGeometry.RelPicard.isAlgEquivZero_fibre_of_range_subset_singleton_of_twoGluedSmoothCurveDegenerations`](thm.html#AlgebraicGeometry.RelPicard.isAlgEquivZero_fibre_of_range_subset_singleton_of_twoGluedSmoothCurveDegenerations) and [`AlgebraicGeometry.RelPicard.isAlgEquivZero_fibre_of_range_subset_singleton_of_twoLineDegenerations`](thm.html#AlgebraicGeometry.RelPicard.isAlgEquivZero_fibre_of_range_subset_singleton_of_twoLineDegenerations), in the construction of the relative Picard functor and of $\operatorname{Pic}^0$ underlying the Néron model input.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_isAlgEquivZero_fibre_of_range_subset_singleton_of_smooth.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_SheafOfModules_Monoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  NeronModelInfra

theorem AlgebraicGeometry.RelPicard.isAlgEquivZero_fibre_of_range_subset_singleton_of_smooth
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c] [Flat c]
    (𝒱 : C.TwoAffineOpenCover)
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (hgoodU : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)),
      Smooth (pullback.snd c x) → Set.range (pullback.fst c x).base ⊆ (U : Set C)) :
    ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
      (L : RigidifiedLineBundle c ε t) (x : T)
      {k₁ : Type u} [Field k₁] [IsAlgClosed k₁] (s₁ : Spec (CommRingCat.of k₁) ⟶ T),
      Set.range ⇑s₁ ⊆ {x} → IsAlgEquivZero (fibreAt c t s₁) (fibreModule c t s₁ L.L) →
      ∀ {k₂ : Type u} [Field k₂] [IsAlgClosed k₂] (s₂ : Spec (CommRingCat.of k₂) ⟶ T),
      Set.range ⇑s₂ ⊆ {x} → Smooth (pullback.snd c (s₂ ≫ t)) →
      IsAlgEquivZero (fibreAt c t s₂) (fibreModule c t s₂ L.L) := by sorry
