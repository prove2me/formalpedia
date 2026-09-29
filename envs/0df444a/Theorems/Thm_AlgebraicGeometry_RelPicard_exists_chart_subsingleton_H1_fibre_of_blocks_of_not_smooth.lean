-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_fibre_of_blocks_of_not_smooth
-- name    : AlgebraicGeometry.RelPicard.exists_chart_subsingleton_H1_fibre_of_blocks_of_not_smooth
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/27d85baa-0959-505d-b6b6-df504b6bf1ce
-- title:
--   Chart killing Čech H¹ on a non-smooth geometric fibre
-- statement:
--   Let $R$ be a commutative ring and $c\colon C\to\operatorname{Spec}R$ proper and flat, equipped with a two-affine open cover $\mathcal V$ of $C$ (a pair of affine opens covering $C$ with affine intersection), and assume that for every $R$-algebra $A$ the structure map $A\to\Gamma(C\times_{\operatorname{Spec}R}\operatorname{Spec}A,\top)$ is bijective. Let $\varepsilon$ be a section of $c$ and $U\subseteq C$ an open with $U\hookrightarrow C\to\operatorname{Spec}R$ smooth of relative dimension $1$, such that $\operatorname{range}\varepsilon\subseteq U$, every smooth geometric fibre lies set-theoretically in $U$, and every geometric fibre is reduced. Let $g$ be such that for every geometric point and every two-affine cover of the corresponding fibre the two-chart Čech $H^1$ of the structure sheaf has $k$-dimension $g$. Assume further that over every algebraically closed $k$ and every $s\colon\operatorname{Spec}k\to\operatorname{Spec}R$ with non-smooth fibre there is a two-line degeneration package (summarised here): two curve models $M_1,M_2$ of $\mathrm{RatFunc}(k)$ over $k$ with closed immersions $i_1,i_2$ into the fibre over $\operatorname{Spec}k$, jointly surjective, meeting exactly in the points $T=a_i$ of $M_1$ and $T=b_i$ of $M_2$ for an injective $a\colon\mathrm{Fin}\,n\to k^\times$ and some $b$, with $\operatorname{pullback} i_1\,i_2$ reduced; a two-affine cover $\mathcal W_0$ of the fibre whose charts pull back to the complements of the point at infinity, respectively of $T=0$, on each model; the point at infinity of $M_1$ equal to the point cut out by $\varepsilon$ on the fibre; $\operatorname{range}i_1$ meeting the preimage of $U$ exactly in the connected component of that point; the nodes outside the preimage of $U$ and all other points of the fibre inside it; and an open $W_1$ of the fibre whose underlying set is the complement of $\operatorname{range}i_2$, with $(i_1^{-1}W_1)\hookrightarrow M_1$ followed by $i_1$ an open immersion. Let $A$ be a Noetherian $R$-algebra, $e,r$ with $g+e=r$ and $2g\le r+1$. Let $B\colon\mathrm{Fin}\,M\to$ commutative $R$-algebras with degrees $\deg i\ge 1$ and $A\otimes_R B_i\simeq A^{\deg i}$ as $A$-algebras, together with closed immersions $z_i\colon\operatorname{Spec}B_i\to C$ over $\operatorname{Spec}R$, with images in $U$, pairwise disjoint, and such that on every geometric fibre the preimage of $\operatorname{range}z_i$ lies in the connected component of the $\varepsilon$-point inside the preimage of $U$. Let $\sigma_i\colon\mathrm{Fin}(\deg i)\to$ sections of the base change $C_A\to\operatorname{Spec}A$, each injective and each factoring through $z_i$ after composition with the projection to $C$. Let $D_\gamma$, indexed by pairs consisting of an injective $a\colon\mathrm{Fin}\,e\to\mathrm{Fin}\,M$ and a choice $m_i\in\mathrm{Fin}(\deg i)$, be relative effective Cartier divisors of degree $e$ on $C_A$ over $\operatorname{Spec}A$ whose ideal is the product of the graph kernels of the $\sigma_{a(j)}(m_{a(j)})$ and whose support lies in the preimage of $U$. Let $b$ bound all $\deg i$ with $r\,b^{e}+e<M$. Finally let $t\colon T\to\operatorname{Spec}A$, let $L$ be a line bundle on $C_A\times_{\operatorname{Spec}A}T$ rigidified along the base-changed section, satisfying `FibrewiseAlgEquivZero`, and let $s\colon\operatorname{Spec}K\to T$ with $K$ algebraically closed be such that the fibre of $C_A$ over $s\circ t$ is not smooth. Then there is an index $i$ for which, for every two-affine open cover $\mathcal W$ of the fibre $(C_A\times_{\operatorname{Spec}A}T)\times_T\operatorname{Spec}K$, the two-chart Čech $H^1$ of the sections of the pullback to that fibre of $L\otimes\big(((\mathcal I_\varepsilon)^r)^{\vee}\otimes \mathcal I_{D_\gamma(i)}\big)$ is a subsingleton, where $\mathcal I_\varepsilon$ is the ideal of the rigidifying section and $D_\gamma(i)$ is pulled back along $t$.
--
--   This is the degenerate-fibre half of the chart-cover statement for the relative Picard functor of a curve with two-line (Deligne–Rapoport type) degenerations: on a non-smooth geometric fibre, one divisor from the combinatorial pool of $e$-fold sums of pool sections already makes the Čech $H^1$ of the twisted line bundle vanish, so that the corresponding chart is available. It is used by [`AlgebraicGeometry.RelPicard.exists_chart_subsingleton_H1_fibre_of_blocks_of_injective`](thm.html#AlgebraicGeometry.RelPicard.exists_chart_subsingleton_H1_fibre_of_blocks_of_injective), where it is combined with the statement for smooth fibres.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_fibre_of_blocks_of_not_smooth.lean

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

theorem AlgebraicGeometry.RelPicard.exists_chart_subsingleton_H1_fibre_of_blocks_of_not_smooth
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
    (b : ℕ) (hdegb : ∀ i, deg i ≤ b) (hMlt : r * b ^ e + e < M)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of A))
    (L : RigidifiedLineBundle (baseChange R c A) (sectionBaseChange A ε) t) (hL : FibrewiseAlgEquivZero L)
    (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (CommRingCat.of K) ⟶ T)
    (hns : ¬ Smooth (pullback.snd (baseChange R c A) (s ≫ t))) :
    ∃ i : ULift.{u} ({a : Fin e → Fin M // Function.Injective a} × (∀ i, Fin (deg i))),
      ∀ 𝒲 : (pullback (pullback.snd (baseChange R c A) t) s).TwoAffineOpenCover,
        Subsingleton (𝒲.sectionsOf (fibreAt (baseChange R c A) t s) (fibreModule (baseChange R c A) t s
          (L.L ⊗ (sectionTwist (baseChange R c A) (sectionBaseChange A ε) t r ⊗
            ((Dγ i).pullbackAlong t (Category.comp_id t)).idealModule)))).H1 := by sorry
