-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_isLFPSurj_relSubPicPresheaf_algEquivZeroCut_baseChange_of_twoGluedSmoothCurveDegenerations
-- name    : AlgebraicGeometry.RelPicard.isLFPSurj_relSubPicPresheaf_algEquivZeroCut_baseChange_of_twoGluedSmoothCurveDegenerations
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/51a72ae9-3f95-563c-a0dc-a661545ea03f
-- title:
--   Surjective finite-presentation half of Pic⁰ for two-glued-curve degenerations
-- statement:
--   Let $R$ be a commutative ring and $c : C \to \operatorname{Spec} R$ a proper flat morphism of schemes, equipped with a cover $\mathcal V$ of $C$ by two affine opens whose intersection is affine. Assume: for every $R$-algebra $A$ the structure map $A \to \Gamma(C\times_{\operatorname{Spec}R}\operatorname{Spec}A,\mathcal O)$ is bijective; $\varepsilon$ is a section of $c$; $U \subseteq C$ is an open whose structure morphism $U \hookrightarrow C \to \operatorname{Spec}R$ is smooth of relative dimension $1$; the image of $\varepsilon$ lies in $U$; for every algebraically closed field $k$ and every $x : \operatorname{Spec} k \to \operatorname{Spec} R$ with smooth fibre, the image of the fibre in $C$ lies in $U$; every geometric fibre $C\times \operatorname{Spec}k$ is reduced; and for a fixed $g \in \mathbb N$, every geometric fibre has $\dim_k H^1 = g$ for the two-chart Čech $H^1$ (the cokernel of the Čech difference map) of its structure sheaf, computed from an arbitrary two-affine open cover. Assume moreover that each non-smooth geometric fibre at $s : \operatorname{Spec}k \to \operatorname{Spec}R$ admits proper smooth-of-relative-dimension-one geometrically integral curves $C_1, C_2$ over $k$ together with closed immersions $i_1, i_2$ into the fibre, over it, such that: the two images cover the fibre; $C_1\times_{C_s}C_2$ is reduced with cardinality $n>0$; the point $\varepsilon(s)$ of the fibre lies in the image of $i_1$ and not of $i_2$; the preimage of $U$ in the fibre is the complement of the image of the crossing locus $C_1\times_{C_s}C_2 \to C_1 \to C_s$; the image of $i_1$ meets that preimage in exactly the connected component of $\varepsilon(s)$ there, and the image of $i_2$ in the remaining part; and there are opens $W_1, W_2$ of the fibre, equal as sets to the complements of the images of $i_2$, respectively $i_1$, such that $i_\nu^{-1}W_\nu \hookrightarrow C_\nu \to C_s$ is an open immersion for $\nu = 1,2$. Then for every Noetherian $R$-algebra $A$ the presheaf on schemes over $\operatorname{Spec}A$ given by classes of rigidified line bundles on the base change $C_A \to \operatorname{Spec}A$, pointed by the induced section $\varepsilon_A$, subject to the condition `algEquivZeroCut` (every geometric fibre of the line bundle is algebraically equivalent to zero), satisfies `AffineLimit.IsLFPSurj`: for every $A$-algebra $B$ and every element $x$ over $\operatorname{Spec}B$ there are a finitely generated $A$-subalgebra $B_0 \subseteq B$ and an element $x_0$ over $\operatorname{Spec}B_0$ restricting to $x$ along $\operatorname{Spec}B \to \operatorname{Spec}B_0$.
--
--   This is the surjectivity half of the assertion that the relative $\mathrm{Pic}^0$ functor of a pointed proper flat curve degenerating into two transversally crossing smooth curves is locally of finite presentation, in the form needed to descend points of the functor to finitely generated subalgebras. It feeds into the construction of representing objects for the $\mathrm{Pic}^0$ subfunctor of such base-changed curves away from finitely many primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_isLFPSurj_relSubPicPresheaf_algEquivZeroCut_baseChange_of_twoGluedSmoothCurveDegenerations.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf
import Definitions.Def_CategoryTheory_OverTotalPresheaf
import Definitions.Def_AlgebraicGeometry_LocalRepresentabilityULift
import Definitions.Def_AlgebraicGeometry_AffineLimit
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivFunctor
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivRestrict
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivTwist2
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  NeronModelInfra

open AlgebraicGeometry.SmoothProperCurve
open AlgebraicCurve

theorem AlgebraicGeometry.RelPicard.isLFPSurj_relSubPicPresheaf_algEquivZeroCut_baseChange_of_twoGluedSmoothCurveDegenerations
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c] [Flat c]
    (𝒱 : C.TwoAffineOpenCover)
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (hεA : Set.range ε.1 ⊆ (U : Set C))
    (hgoodU : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)),
      Smooth (pullback.snd c x) → Set.range (pullback.fst c x).base ⊆ (U : Set C))
    (hgred : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)), IsReduced (pullback c x))
    (g : ℕ)
    (hg : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover),
      Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
        (SheafOfModules.unit (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).ringCatSheaf)).H1 = g)
    (hbad : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)), ¬ Smooth (pullback.snd c s) →
      ∃ (C₁ C₂ : Scheme.{u}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
        (_ : IsProper c₁) (_ : SmoothOfRelativeDimension 1 c₁) (_ : GeometricallyIntegral c₁)
        (_ : IsProper c₂) (_ : SmoothOfRelativeDimension 1 c₂) (_ : GeometricallyIntegral c₂)
        (i₁ : SchemeHomOver c₁ (pullback.snd c s)) (i₂ : SchemeHomOver c₂ (pullback.snd c s))
        (_ : IsClosedImmersion i₁.1) (_ : IsClosedImmersion i₂.1) (n : ℕ),
        (∀ z : ↥(pullback c s), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base) ∧
        IsReduced (pullback i₁.1 i₂.1) ∧ Nat.card ↥(pullback i₁.1 i₂.1) = n ∧ 0 < n ∧
        ((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k) ∈ Set.range i₁.1.base \ Set.range i₂.1.base ∧
        ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) =
          (Set.range (pullback.fst i₁.1 i₂.1 ≫ i₁.1).base)ᶜ ∧
        Set.range i₁.1.base ∩ ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) =
          connectedComponentIn ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s))
            (((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k)) ∧
        Set.range i₂.1.base ∩ ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) =
          ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) \
            connectedComponentIn ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s))
              (((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k)) ∧
        (∃ W₁ : (pullback c s).Opens, (W₁ : Set ↥(pullback c s)) = (Set.range i₂.1.base)ᶜ ∧
          IsOpenImmersion ((i₁.1 ⁻¹ᵁ W₁).ι ≫ i₁.1)) ∧
        (∃ W₂ : (pullback c s).Opens, (W₂ : Set ↥(pullback c s)) = (Set.range i₁.1.base)ᶜ ∧
          IsOpenImmersion ((i₂.1 ⁻¹ᵁ W₂).ι ≫ i₂.1)))
    (A : Type u) [CommRing A] [Algebra R A] [IsNoetherianRing A] :
    AffineLimit.IsLFPSurj (relSubPicPresheaf (baseChange R c A) (sectionBaseChange A ε) (algEquivZeroCut (baseChange R c A) (sectionBaseChange A ε))) := by sorry
