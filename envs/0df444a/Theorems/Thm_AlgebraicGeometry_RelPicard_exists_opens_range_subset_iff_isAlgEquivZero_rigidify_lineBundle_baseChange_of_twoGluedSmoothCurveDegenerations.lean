-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_opens_range_subset_iff_isAlgEquivZero_rigidify_lineBundle_baseChange_of_twoGluedSmoothCurveDegenerations
-- name    : AlgebraicGeometry.RelPicard.exists_opens_range_subset_iff_isAlgEquivZero_rigidify_lineBundle_baseChange_of_twoGluedSmoothCurveDegenerations
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/b7145a6a-dcac-57ca-bb50-f3bbf5f8bb55
-- title:
--   Openness of the algebraic-equivalence locus for 𝒪(D-E_T)
-- statement:
--   Let $R$ be a commutative ring and $c\colon C\to\operatorname{Spec}R$ a proper flat morphism, equipped with a two-affine open cover $\mathcal V$ of $C$ (two affine opens covering $C$ with affine intersection), and assume that for every $R$-algebra $A$ the structure map $A\to\Gamma(C\times_{\operatorname{Spec}R}\operatorname{Spec}A,\mathcal O)$ is bijective. Let $\varepsilon$ be a section of $c$, let $U\subseteq C$ be an open whose composite $U\hookrightarrow C\to\operatorname{Spec}R$ is smooth of relative dimension $1$, with the image of $\varepsilon$ contained in $U$, and assume: for every algebraically closed field $k$ and every $x\colon\operatorname{Spec}k\to\operatorname{Spec}R$ with smooth fibre, the image of $C_x\to C$ lies in $U$; every geometric fibre is reduced; for some fixed $g\in\mathbb N$, every geometric fibre (formed over the identity of $\operatorname{Spec}R$) has $k$-dimension $g$ for the $H^1$ of the two-chart Čech complex of its structure sheaf, computed with any two-affine open cover; and every non-smooth geometric fibre $C_s$ admits two proper smooth geometrically integral curves $C_1,C_2$ over $k$ with closed immersions $i_1,i_2$ over $C_s$ whose images cover $C_s$, with $C_1\times_{C_s}C_2$ reduced and of cardinality $n>0$, with $\varepsilon(s)$ in the image of $i_1$ and not of $i_2$, with $U_s$ equal to the complement of the image of the crossing locus, with the image of $i_1$ meeting $U_s$ in the connected component of $\varepsilon(s)$ in $U_s$ and the image of $i_2$ meeting $U_s$ in the complement of that component, and with each $i_\nu$ restricted over the complement of the other image an open immersion. Fix a Noetherian $R$-algebra $A$, an index type $\iota$, naturals $e,\rho$, a relative effective Cartier divisor $E$ of degree $\rho$ on $C_A$ over $\operatorname{Spec}A$ supported in the preimage of $U$, and a family $D_{\gamma}\colon\iota\to$ relative effective Cartier divisors of degree $e$ on $C_A$ over $\operatorname{Spec}A$, each supported in the preimage of $U$. The conclusion is: for every $i\in\iota$, every $T$ with $t\colon T\to\operatorname{Spec}A$ locally of finite type, every relative effective Cartier divisor $D$ of degree $\rho$ on $C_A$ over $t$ and every $D_0$ of degree $g$ over $t$ supported in the preimage of $U$, such that the ideal sheaf of $D$ is the product of that of $D_0$ with that of the pullback of $D_{\gamma}(i)$ along $t$, there is an open $W\subseteq T$ such that for every algebraically closed field $k$ and every $s\colon\operatorname{Spec}k\to T$ the image of $s$ lies in $W$ if and only if the restriction to the fibre over $s$ of the rigidification along the section induced by $\varepsilon$ (tensoring with the pullback of the dual of the pullback along that section) of the dual of the ideal module of $D$ tensored with the ideal module of the pullback of $E$ along $t$ is algebraically equivalent to zero, i.e. there are a locally of finite type geometrically integral $k$-scheme $T'$, an invertible module $M$ on $C_{A}\times_T T'$ and two sections of $T'$ over $k$ along which $M$ pulls back to the structure sheaf and to that bundle respectively.
--
--   This is the openness of the locus in the base $T$ over which the rigidified Abel–Jacobi bundle $\mathcal O(D-E_T)$ on the base-changed curve lies in the algebraic-equivalence-zero part of the relative Picard functor, for a family degenerating along the non-smooth locus into two smooth curves crossing at finitely many points. It supplies the cut hypothesis used in the construction of charts for the relative $\operatorname{Pic}^0$ of such a family, and is cited by the theorem producing, away from each prime, representing data for the algebraic-equivalence cut of the base-changed relative sub-Picard functor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_opens_range_subset_iff_isAlgEquivZero_rigidify_lineBundle_baseChange_of_twoGluedSmoothCurveDegenerations.lean

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
import Definitions.Def_AlgebraicGeometry_ModulesRigidify

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  NeronModelInfra

open AlgebraicGeometry.SmoothProperCurve AlgebraicCurve

theorem AlgebraicGeometry.RelPicard.exists_opens_range_subset_iff_isAlgEquivZero_rigidify_lineBundle_baseChange_of_twoGluedSmoothCurveDegenerations
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
    (A : Type u) [CommRing A] [Algebra R A] [IsNoetherianRing A]
    {ι : Type u} (e ρ : ℕ)

    (E : RelEffCartierDiv (baseChange R c A) ρ (𝟙 (Spec (CommRingCat.of A)))) (hEU : E.SupportedIn (pullback.fst c (specMap R A) ⁻¹ᵁ U))
    (Dγ : ι → RelEffCartierDiv (baseChange R c A) e (𝟙 (Spec (CommRingCat.of A))))
    (hDγU : ∀ i, (Dγ i).SupportedIn (pullback.fst c (specMap R A) ⁻¹ᵁ U)) :
    ∀ (i : ι) ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of A)) [LocallyOfFiniteType t]
      (D : RelEffCartierDiv (baseChange R c A) ρ t) (D₀ : RelEffCartierDiv (baseChange R c A) g t), D₀.SupportedIn (pullback.fst c (specMap R A) ⁻¹ᵁ U) →
      D.I = D₀.I * ((Dγ i).pullbackAlong t (Category.comp_id t)).I →
      ∃ W : T.Opens, ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T),
        Set.range ⇑s ⊆ (W : Set T) ↔
          IsAlgEquivZero (fibreAt (baseChange R c A) t s)
            ((Scheme.Modules.pullback (pullback.fst (pullback.snd (baseChange R c A) t) s)).obj (Scheme.Modules.rigidify (RelPicard.rigSection (baseChange R c A) t (sectionBaseChange A ε)) (pullback.snd (baseChange R c A) t)
              (D.lineBundle ⊗ (E.pullbackAlong t (Category.comp_id t)).idealModule))) := by sorry
