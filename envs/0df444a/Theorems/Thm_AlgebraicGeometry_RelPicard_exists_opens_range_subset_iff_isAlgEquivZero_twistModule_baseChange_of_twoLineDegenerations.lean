-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_opens_range_subset_iff_isAlgEquivZero_twistModule_baseChange_of_twoLineDegenerations
-- name    : AlgebraicGeometry.RelPicard.exists_opens_range_subset_iff_isAlgEquivZero_twistModule_baseChange_of_twoLineDegenerations
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/98eb1c21-556a-50b3-bcb7-772872bb10ca
-- title:
--   Openness of the algebraically-trivial locus for twisted divisor bundles
-- statement:
--   Let $R$ be a commutative ring and $c\colon C\to\operatorname{Spec}R$ a proper flat morphism, together with: a two-affine open cover $\mathcal V$ of $C$ (two affine opens whose union is $C$ and whose intersection is affine); the hypothesis that for every $R$-algebra $A$ the structure map $A\to\Gamma(C\times_{\operatorname{Spec}R}\operatorname{Spec}A,\top)$ is bijective; a section $\varepsilon$ of $c$ over $\operatorname{Spec}R$; an open $U\subseteq C$ with $U\hookrightarrow C\to\operatorname{Spec}R$ smooth of relative dimension $1$, whose set of points contains the image of $\varepsilon$ and contains the image in $C$ of every smooth geometric fibre; the hypothesis that all geometric fibres $C\times_{\operatorname{Spec}R}\operatorname{Spec}k$ ($k$ algebraically closed) are reduced; a natural number $g$ such that for every geometric point and every two-affine cover of the corresponding fibre the $k$-dimension of the first Čech cohomology group of the structure sheaf equals $g$; and, for every non-smooth geometric fibre $C_s$, two-line degeneration data, namely closed immersions $i_1,i_2$ into $C_s$ of the curves underlying `CurveModel`s $M_1,M_2$ over $k$ with function field $\mathrm{RatFunc}\,k$, an integer $n$ and points $a,b\colon \mathrm{Fin}\,n\to k^\times$ with $a$ injective, and a two-affine cover $\mathcal W_0$ of $C_s$, subject to conditions (summarised here) saying that $i_1,i_2$ are morphisms over $\operatorname{Spec}k$ whose images cover $C_s$ and meet exactly in the $n$ glued pairs of points $a_i\leftrightarrow b_i$, that $M_1.C\times_{C_s}M_2.C$ is reduced, that the preimages under $i_1,i_2$ of the two charts of $\mathcal W_0$ are the complements of the points at infinity, respectively at $0$, that $i_1$ carries the point at infinity to the fibre point of $\varepsilon$, that the image of $i_1$ meets the preimage of $U$ exactly in the connected component of that point, that the glued points lie outside the preimage of $U$ while every other point of $C_s$ lies inside it, and that the complement of the image of $i_2$ is open with $i_1$ restricting to an open immersion over it. Let $A$ be a Noetherian $R$-algebra, $\iota$ a type, $e,r$ natural numbers, and let $D_\gamma\colon\iota\to$ relative effective Cartier divisors of degree $e$ on $C_A$ relative to the identity of $\operatorname{Spec}A$ (ideal sheaf data whose closed subscheme is finite, flat and locally of finite presentation over the base with all fibre ranks $e$), each supported in the preimage of $U$. The conclusion: for every $i\in\iota$, every $t\colon T\to\operatorname{Spec}A$ locally of finite type, every relative effective Cartier divisor $D$ of degree $r$ and every $D_0$ of degree $g$ on $C_A\times_{\operatorname{Spec}A}T$ relative to $t$ with $D_0$ supported in the preimage of $U$ and $I_D=I_{D_0}\cdot I_{D_\gamma(i)_T}$, there is an open $W\subseteq T$ such that for every algebraically closed field $k$ and every $s\colon\operatorname{Spec}k\to T$ the image of $s$ lies in $W$ if and only if the pullback to the geometric fibre of the rigidified twist of $D$ by the base-changed section $\varepsilon_A$ — the tensor product of the inverse of the ideal sheaf of $D$ with the $r$-th power of the ideal sheaf of the rigidifying section, tensored with the pullback along the projection of the dual of its restriction along that section — satisfies `IsAlgEquivZero` over the fibre, i.e. there exist a locally of finite type, geometrically integral $T'\to\operatorname{Spec}k$, an invertible module on the product of the fibre with $T'$, and two $k$-points of $T'$ at which its restriction becomes isomorphic to the unit module, respectively to the given module.
--
--   This is the openness, on a base-changed curve with two-line degenerations, of the locus where the twisted bundle $\mathcal O(D-r\varepsilon)$ attached to a divisor of the shape $D_0+D_\gamma$ is algebraically equivalent to zero. It supplies the open-cut input, at level $A$, for the construction of the relative $\mathrm{Pic}^0$ subfunctor via theta-divisor charts.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_opens_range_subset_iff_isAlgEquivZero_twistModule_baseChange_of_twoLineDegenerations.lean

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
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  NeronModelInfra

open AlgebraicGeometry.SmoothProperCurve AlgebraicCurve

theorem AlgebraicGeometry.RelPicard.exists_opens_range_subset_iff_isAlgEquivZero_twistModule_baseChange_of_twoLineDegenerations
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
    (hbad : ∀ (k : Type u) [Field k] [IsAlgClosed k] [DecidableEq (RatFunc k)]
      (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)), ¬ Smooth (pullback.snd c s) →
      ∃ (M₁ M₂ : CurveModel k (RatFunc k)) (i₁ : M₁.C ⟶ pullback c s) (i₂ : M₂.C ⟶ pullback c s)
        (_ : IsClosedImmersion i₁) (_ : IsClosedImmersion i₂)
        (n : ℕ) (a b : Fin n → kˣ) (𝒲₀ : (pullback c s).TwoAffineOpenCover),
        i₁ ≫ pullback.snd c s = M₁.toBase ∧ i₂ ≫ pullback.snd c s = M₂.toBase ∧
        Set.range i₁.base ∪ Set.range i₂.base = Set.univ ∧
        Function.Injective a ∧
        (∀ i, i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 =
          i₂.base (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k (b i : k))).1) ∧
        (∀ (p : M₁.C) (q : M₂.C), i₁.base p = i₂.base q →
          ∃ i, p = (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 ∧
            q = (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k (b i : k))).1) ∧
        IsReduced (pullback i₁ i₂) ∧
        ((i₁ ⁻¹ᵁ 𝒲₀.U0 : M₁.C.Opens) : Set M₁.C) =
          {(M₁.placeEquiv.symm (RationalFunctionField.placeInfty k)).1}ᶜ ∧
        ((i₂ ⁻¹ᵁ 𝒲₀.U0 : M₂.C.Opens) : Set M₂.C) =
          {(M₂.placeEquiv.symm (RationalFunctionField.placeInfty k)).1}ᶜ ∧
        ((i₁ ⁻¹ᵁ 𝒲₀.U1 : M₁.C.Opens) : Set M₁.C) =
          {(M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k 0)).1}ᶜ ∧
        ((i₂ ⁻¹ᵁ 𝒲₀.U1 : M₂.C.Opens) : Set M₂.C) =
          {(M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k 0)).1}ᶜ ∧
        i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeInfty k)).1 = ((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k) ∧
        Set.range i₁.base ∩ ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) =
          connectedComponentIn ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) (((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k)) ∧
        (∀ i, i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 ∉
          (pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens)) ∧
        (∀ y : ↥(pullback c s),
          (∀ i, y ≠ i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1) →
            y ∈ (pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens)) ∧
        (∃ W₁ : (pullback c s).Opens, (W₁ : Set ↥(pullback c s)) = (Set.range i₂.base)ᶜ ∧
          IsOpenImmersion ((i₁ ⁻¹ᵁ W₁).ι ≫ i₁)))
    (A : Type u) [CommRing A] [Algebra R A] [IsNoetherianRing A]
    {ι : Type u} (e r : ℕ) (Dγ : ι → RelEffCartierDiv (baseChange R c A) e (𝟙 (Spec (CommRingCat.of A))))
    (hDγU : ∀ i, (Dγ i).SupportedIn (pullback.fst c (specMap R A) ⁻¹ᵁ U)) :
    ∀ (i : ι) ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of A)) [LocallyOfFiniteType t]
      (D : RelEffCartierDiv (baseChange R c A) r t) (D₀ : RelEffCartierDiv (baseChange R c A) g t), D₀.SupportedIn (pullback.fst c (specMap R A) ⁻¹ᵁ U) →
      D.I = D₀.I * ((Dγ i).pullbackAlong t (Category.comp_id t)).I →
      ∃ W : T.Opens, ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T),
        Set.range ⇑s ⊆ (W : Set T) ↔
          IsAlgEquivZero (fibreAt (baseChange R c A) t s)
            ((Scheme.Modules.pullback (pullback.fst (pullback.snd (baseChange R c A) t) s)).obj (D.twistModule (baseChange R c A) (sectionBaseChange A ε))) := by sorry
