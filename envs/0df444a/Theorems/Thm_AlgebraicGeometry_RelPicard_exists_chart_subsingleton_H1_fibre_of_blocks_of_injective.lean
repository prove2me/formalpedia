-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_fibre_of_blocks_of_injective
-- name    : AlgebraicGeometry.RelPicard.exists_chart_subsingleton_H1_fibre_of_blocks_of_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/835b8907-9763-5ccb-bb26-5ce8da924b8d
-- title:
--   Chart divisors from a split pool of sections cover Pic⁰
-- statement:
--   Fix a commutative ring $R$ and a proper flat morphism $c\colon C\to\operatorname{Spec}R$, together with: a two-affine open cover $\mathcal V$ of $C$ (two affine opens with affine intersection whose union is $C$); the hypothesis `hH0` that for every $R$-algebra $A$ the structure map $A\to\Gamma(C\times_{\operatorname{Spec}R}\operatorname{Spec}A,\top)$ is bijective; a section $\varepsilon$ of $c$; an open $U\subseteq C$ with $U\hookrightarrow C\to\operatorname{Spec}R$ smooth of relative dimension $1$, containing the image of $\varepsilon$, containing the image of every smooth geometric fibre, all geometric fibres being reduced; a natural number $g$ such that for every algebraically closed $k$, every $x\colon\operatorname{Spec}k\to\operatorname{Spec}R$ and every two-affine open cover of the fibre, the $k$-dimension of the Čech $H^1$ of the structure sheaf is $g$; and the hypothesis `hbad` describing each non-smooth geometric fibre as a transversal gluing of two curve models over $k(T)$: closed immersions $i_1,i_2$ whose images cover the fibre, glued along $n$ pairs of points $a_i,b_i\in k^\times$ (and only there), with reduced intersection, with $\mathcal W_0$-charts the complements of $\infty$ and $0$ on each model, with $i_1(\infty)$ the $\varepsilon$-point of the fibre, with the image of $i_1$ meeting the preimage of $U$ exactly in the connected component of the $\varepsilon$-point, with the nodes the only points outside the preimage of $U$, and with the complement of the image of $i_2$ open and $i_1$ an open immersion over it. Fix further a Noetherian $R$-algebra $A$, naturals $e,r$ with $g+e=r$ and $2g\le r+1$, finitely many $R$-algebras $B_i$ ($i<M$) of degrees $\deg i\ge 1$ with $A\otimes_R B_i\cong A^{\deg i}$ as $A$-algebras, closed immersions $z_i\colon\operatorname{Spec}B_i\to C$ over $\operatorname{Spec}R$ with images in $U$, pairwise disjoint, and contained, in every geometric fibre, in the connected component of the $\varepsilon$-point inside the preimage of $U$; for each $i$ an injective family $\sigma_{i,m}$ ($m<\deg i$) of sections of the base change $C_A\to\operatorname{Spec}A$, each factoring through $z_i$; a family $D_\gamma$ of relative effective Cartier divisors of degree $e$ on $C_A$ over $\operatorname{Spec}A$, indexed by pairs consisting of an injective $a\colon\mathrm{Fin}\,e\to\mathrm{Fin}\,M$ and a choice $m$ of one section in each block, whose ideal is the product of the kernel ideals of the graphs of the $\sigma_{a(j),m(a(j))}$ and which are supported in the preimage of $U$; and $b$ with $\deg i\le b$ for all $i$ and $r\,b^{e}+e<M$. Then for every scheme $T$, every $t\colon T\to\operatorname{Spec}A$ and every line bundle $L$ on $C_A\times_{\operatorname{Spec}A}T$ rigidified along the base change of $\varepsilon$ and satisfying `FibrewiseAlgEquivZero` (over every algebraically closed field point of $T$ its restriction to the fibre is algebraically equivalent to zero in the sense of `IsAlgEquivZero`), and for every field $k$ and every $s\colon\operatorname{Spec}k\to T$, there is an index $\gamma$ such that for every two-affine open cover of the fibre the Čech $H^1$ of $L\otimes\mathcal O(r\varepsilon)\otimes\mathcal O(-D_\gamma)$ on that fibre is a subsingleton, where $\mathcal O(r\varepsilon)$ is `sectionTwist` of the rigidifying section and $\mathcal O(-D_\gamma)$ is the ideal module of the pullback of $D_\gamma$ along $t$.
--
--   This is Milne's statement that the charts $J^{\gamma}$ cover $\mathrm{Pic}^0$, here in the form of the covering hypothesis needed to chart the algebraic-equivalence-zero cut of the relative Picard functor of a proper flat curve with at worst two-component degenerate fibres, after base change to a Noetherian algebra $A$ over which the chosen pool of blocks splits into sections. It is used by [`AlgebraicGeometry.RelPicard.forall_prime_exists_representsRelSubPic_algEquivZeroCut_baseChange_away_of_smoothLocus_of_twoLineDegenerations`](thm.html#AlgebraicGeometry.RelPicard.forall_prime_exists_representsRelSubPic_algEquivZeroCut_baseChange_away_of_smoothLocus_of_twoLineDegenerations), which turns the chart family into a representability statement for that cut.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_fibre_of_blocks_of_injective.lean

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

open AlgebraicGeometry.SmoothProperCurve
open AlgebraicCurve

theorem AlgebraicGeometry.RelPicard.exists_chart_subsingleton_H1_fibre_of_blocks_of_injective
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
    (A : Type u) [CommRing A] [Algebra R A] [IsNoetherianRing A] (e r : ℕ) (hr : g + e = r)
    {M : ℕ} (B : Fin M → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    (deg : Fin M → ℕ) (hdeg : ∀ i, 1 ≤ deg i) (φ : ∀ i, TensorProduct R A (B i) ≃ₐ[A] (Fin (deg i) → A))
    (z : ∀ i, Spec (CommRingCat.of (B i)) ⟶ C) [∀ i, IsClosedImmersion (z i)]
    (hz : ∀ i, z i ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R (B i))))
    (hzU : ∀ i, Set.range (z i).base ⊆ (U : Set C))
    (hzdisj : Pairwise fun i j => Disjoint (Set.range (z i).base) (Set.range (z j).base))
    (hzε : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) (i : Fin M),
      (pullback.fst c s).base ⁻¹' Set.range (z i).base ⊆
        connectedComponentIn ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s))
          (((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k)))
    (σ : ∀ i, Fin (deg i) → SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (baseChange R c A))
    (hσfac : ∀ i m, ∃ y : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of (B i)),
      (σ i m).1 ≫ pullback.fst c (specMap R A) = y ≫ z i)
    (Dγ : ULift.{u} ({a : Fin e → Fin M // Function.Injective a} × (∀ i, Fin (deg i))) →
      RelEffCartierDiv (baseChange R c A) e (𝟙 (Spec (CommRingCat.of A))))
    (hDγI : ∀ am, (Dγ am).I = prodKerGraph (baseChange R c A)
      (fun j => (σ (am.down.1.1 j) (am.down.2 (am.down.1.1 j))).1)
      (fun j => (σ (am.down.1.1 j) (am.down.2 (am.down.1.1 j))).2))
    (hDγU : ∀ am, (Dγ am).SupportedIn (pullback.fst c (specMap R A) ⁻¹ᵁ U))
    (hσinj : ∀ i, Function.Injective (σ i))
    (hgr : 2 * g ≤ r + 1)
    (b : ℕ) (hdegb : ∀ i, deg i ≤ b) (hMlt : r * b ^ e + e < M) :
    ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of A)) (L : RigidifiedLineBundle (baseChange R c A) (sectionBaseChange A ε) t),
      FibrewiseAlgEquivZero L → ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T),
      ∃ i : ULift.{u} ({a : Fin e → Fin M // Function.Injective a} × (∀ i, Fin (deg i))), ∀ (𝒲 : (pullback (pullback.snd (baseChange R c A) t) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt (baseChange R c A) t s) (fibreModule (baseChange R c A) t s
          (L.L ⊗ (sectionTwist (baseChange R c A) (sectionBaseChange A ε) t r ⊗ ((Dγ i).pullbackAlong t (Category.comp_id t)).idealModule)))).H1 := by sorry
