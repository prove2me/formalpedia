-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_eulerChar_pullback_firstLine_sectionTwist_tensor_idealModule_eq
-- name    : AlgebraicGeometry.RelPicard.eulerChar_pullback_firstLine_sectionTwist_tensor_idealModule_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/2136140e-fe18-5dc0-896f-e311afa7adeb
-- title:
--   Euler characteristic g+1 on the first line of a degenerate fibre
-- statement:
--   Let $R$ be a commutative ring, $c\colon C\to\operatorname{Spec}R$ a proper morphism of schemes, $U\subseteq C$ an open whose inclusion followed by $c$ is smooth of relative dimension $1$, and $\varepsilon$ a section of $c$ (a morphism $\operatorname{Spec}R\to C$ composing with $c$ to the identity) whose image lies in $U$; let $e,r,g$ be natural numbers with $g+e=r$, and let $D_\gamma$ be a relative effective Cartier divisor for $c$ over the identity of $\operatorname{Spec}R$ of degree $e$ — an ideal sheaf datum on $C\times_R\operatorname{Spec}R$ whose closed subscheme is finite, flat and locally of finite presentation over the base with all fibre ranks $e$ — whose support is contained in the preimage of $U$ under the first projection. Let $k$ be an algebraically closed field and $s\colon\operatorname{Spec}k\to\operatorname{Spec}R$ a point with reduced fibre $X:=C\times_{\operatorname{Spec}R}\operatorname{Spec}k$. Let $M_1,M_2$ be curve models over $k$ with function field $k(t)=\mathrm{RatFunc}\ k$ (integral proper smooth relative-dimension-one curves together with an isomorphism of their function field with $k(t)$ over $k$ and a bijection between closed points and places), given with closed immersions $i_1\colon M_1.C\to X$, $i_2\colon M_2.C\to X$ compatible with the structure morphisms ($i_j$ followed by the second projection is $M_j.\mathrm{toBase}$), and let $\mathcal W_0$ be a two-affine open cover of $X$ and $a,b\colon\mathrm{Fin}\ n\to k^\times$. The degeneration hypotheses are: the images of $i_1$ and $i_2$ cover $X$; $a$ is injective; for each $i$ the closed point of $M_1$ at the place of $a_i$ and the closed point of $M_2$ at the place of $b_i$ have the same image in $X$; conversely any two points with equal images arise this way; $M_1.C\times_X M_2.C$ is reduced; the preimages under $i_1$ and $i_2$ of $\mathcal W_0.U_0$ (respectively $\mathcal W_0.U_1$) are the complements of the points at the place at infinity (respectively at the place of $0$); $i_1$ maps the point at infinity to the image of the closed point under the $k$-point of $X$ determined by $\varepsilon$ and $s$; the intersection of the image of $i_1$ with the preimage of $U$ is exactly the connected component of that preimage containing this $\varepsilon$-point; no node image lies in the preimage of $U$, while every point of $X$ that is not such a node image does; there is an open $W_1\subseteq X$ whose underlying set is the complement of the image of $i_2$ and for which the inclusion of $i_1^{-1}W_1$ followed by $i_1$ is an open immersion; and the preimage in $X$ of the image of the closed subscheme of $D_\gamma$ is contained in that same connected component. Under these hypotheses, for every two-affine open cover $\mathcal W'$ of $M_1.C$, the two-chart Čech complex of $k$-modules of sections over the two charts of the pullback along $i_1$ of $\mathcal{O}(r\varepsilon)\otimes\mathcal I_{D_\gamma}$ — that is, of the dual of the $r$-th power of the ideal sheaf of the $\varepsilon$-section on $X$, tensored with the ideal sheaf module of the base change of $D_\gamma$ along $s$ — satisfies $$\dim_k H^0-\dim_k H^1=g+1,$$ where $H^0$ is the kernel and $H^1$ the cokernel of the Čech difference map from the product of the sections over the two charts to the sections over their intersection.
--
--   This computes, for the bad (two-line) geometric fibres of a semistable family, the Euler characteristic of the restriction to the first line of the twist $\mathcal O(r\varepsilon)\otimes\mathcal I_{D_\gamma}$, in the two-chart Čech presentation used throughout for coherent cohomology of curves. It is the specialisation to $T=\operatorname{Spec}k$ and trivial line bundle of the general Euler-characteristic formula `eulerChar_pullback_fibreModule_tensor_sectionTwist_tensor_idealModule_eq`, and it feeds the analysis of the non-smooth stratum in `exists_isOpen_inter_preimage_eq_setOf_isAlgEquivZero_fibre_of_smoothLocus_of_twoLineDegenerations` and `exists_relEffCartierDiv_I_eq_zeroSchemeIdeal_chartModule_fibre_of_not_smooth_of_isReduced`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_eulerChar_pullback_firstLine_sectionTwist_tensor_idealModule_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  NeronModelInfra AlgebraicCurve

theorem AlgebraicGeometry.RelPicard.eulerChar_pullback_firstLine_sectionTwist_tensor_idealModule_eq
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (hεU : Set.range ε.1 ⊆ (U : Set C))
    (e r : ℕ) (g : ℕ) (hr : g + e = r)
    (Dγ : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R)))) (hDγU : Dγ.SupportedIn U)
    (k : Type u) [Field k] [IsAlgClosed k] [DecidableEq (RatFunc k)]
    (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) [IsReduced (pullback c s)]
    (M₁ M₂ : CurveModel k (RatFunc k)) (i₁ : M₁.C ⟶ pullback c s) (i₂ : M₂.C ⟶ pullback c s)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (n : ℕ) (a b : Fin n → kˣ) (𝒲₀ : (pullback c s).TwoAffineOpenCover)
    (hi₁ : i₁ ≫ pullback.snd c s = M₁.toBase)
    (hi₂ : i₂ ≫ pullback.snd c s = M₂.toBase)
    (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    (ha : Function.Injective a)
    (hnode : ∀ i, i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 =
          i₂.base (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k (b i : k))).1)
    (hinter : ∀ (p : M₁.C) (q : M₂.C), i₁.base p = i₂.base q →
          ∃ i, p = (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 ∧
          q = (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k (b i : k))).1)
    (htrans : IsReduced (pullback i₁ i₂))
    (hU0₁ : ((i₁ ⁻¹ᵁ 𝒲₀.U0 : M₁.C.Opens) : Set M₁.C) =
          {(M₁.placeEquiv.symm (RationalFunctionField.placeInfty k)).1}ᶜ)
    (hU0₂ : ((i₂ ⁻¹ᵁ 𝒲₀.U0 : M₂.C.Opens) : Set M₂.C) =
          {(M₂.placeEquiv.symm (RationalFunctionField.placeInfty k)).1}ᶜ)
    (hU1₁ : ((i₁ ⁻¹ᵁ 𝒲₀.U1 : M₁.C.Opens) : Set M₁.C) =
          {(M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k 0)).1}ᶜ)
    (hU1₂ : ((i₂ ⁻¹ᵁ 𝒲₀.U1 : M₂.C.Opens) : Set M₂.C) =
          {(M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k 0)).1}ᶜ)
    (hεinf : i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeInfty k)).1 = ((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k))
    (hcomp : Set.range i₁.base ∩ ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) =
          connectedComponentIn ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) (((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k)))
    (hnodesU : ∀ i, i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 ∉
          (pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens))
    (hnonnodes : ∀ y : ↥(pullback c s),
          (∀ i, y ≠ i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1) →
            y ∈ (pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens))
    (hW₁ : ∃ W₁ : (pullback c s).Opens, (W₁ : Set ↥(pullback c s)) = (Set.range i₂.base)ᶜ ∧
          IsOpenImmersion ((i₁ ⁻¹ᵁ W₁).ι ≫ i₁))
    (hDγcomp : (pullback.fst c s).base ⁻¹' ((Dγ.I.subschemeι ≫ pullback.fst c (𝟙 _)).base '' Set.univ) ⊆
        connectedComponentIn ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s))
          (((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k))) :
    ∀ 𝒲' : M₁.C.TwoAffineOpenCover,
      (Module.finrank k ↥(𝒲'.sectionsOf M₁.toBase ((Scheme.Modules.pullback i₁).obj
          (sectionTwist c ε s r ⊗ (Dγ.pullbackAlong s (Category.comp_id s)).idealModule))).H0 : ℤ) -
        Module.finrank k (𝒲'.sectionsOf M₁.toBase ((Scheme.Modules.pullback i₁).obj
          (sectionTwist c ε s r ⊗ (Dγ.pullbackAlong s (Category.comp_id s)).idealModule))).H1 = g + 1 := by sorry
