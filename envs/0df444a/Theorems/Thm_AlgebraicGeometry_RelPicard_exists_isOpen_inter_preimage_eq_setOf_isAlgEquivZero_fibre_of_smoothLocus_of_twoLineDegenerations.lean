-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_isOpen_inter_preimage_eq_setOf_isAlgEquivZero_fibre_of_smoothLocus_of_twoLineDegenerations
-- name    : AlgebraicGeometry.RelPicard.exists_isOpen_inter_preimage_eq_setOf_isAlgEquivZero_fibre_of_smoothLocus_of_twoLineDegenerations
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/2e80b546-57ea-573a-87b1-73deac3bd5ed
-- title:
--   Openness of the Pic⁰ locus along the degeneration locus
-- statement:
--   Let $R$ be a Noetherian commutative ring and $c\colon C\to\operatorname{Spec}R$ a proper flat morphism of schemes, equipped with a two-affine open cover $\mathcal V$ of $C$ (two affine opens with affine intersection covering $C$). Assume: (i) for every $R$-algebra $A$ the structural map $A\to\Gamma(C\times_{\operatorname{Spec}R}\operatorname{Spec}A,\top)$ is bijective; (ii) an open $U\subseteq C$ with $U\hookrightarrow C\to\operatorname{Spec}R$ smooth of relative dimension $1$, and a section $\varepsilon$ of $c$ (a morphism with $c\circ\varepsilon=\mathrm{id}$) whose image lies in $U$; (iii) for every algebraically closed field $k$ and every $k$-point $x$ of $\operatorname{Spec}R$ with smooth fibre, the image of the fibre in $C$ lies in $U$; (iv) all geometric fibres are reduced; (v) a natural number $g$ such that for every algebraically closed $k$, every $k$-point $x$ and every two-affine cover $\mathcal W$ of the fibre, the $k$-dimension of the Čech $H^1$ of the structure sheaf computed from $\mathcal W$ equals $g$; (vi) for every algebraically closed $k$ and every $k$-point $s$ with non-smooth fibre $C_s$, a presentation of $C_s$ as two glued coordinatised projective lines: curve models $M_1,M_2$ over $k$ with function field $\operatorname{RatFunc}k$, closed immersions $i_1,i_2\colon M_j\to C_s$ over $\operatorname{Spec}k$ whose images cover $C_s$, an injective $a\colon \mathrm{Fin}\,n\to k^\times$ and $b\colon\mathrm{Fin}\,n\to k^\times$ such that $i_1$ and $i_2$ identify the points at the places $a_i$ and $b_i$ and these are the only coincidences, with $\operatorname{pullback} i_1\,i_2$ reduced, with the two charts of a cover $\mathcal W_0$ of $C_s$ pulling back to the complements of the points at infinity and at $0$ on both $M_j$, with $i_1$ sending the point at infinity of $M_1$ to the point cut out by $\varepsilon$ on $C_s$, with the image of $i_1$ meeting the preimage of $U$ exactly in the connected component of that preimage containing the $\varepsilon$-point, with the glue points lying outside the preimage of $U$ and every non-glue point inside it, and with an open $W_1\subseteq C_s$ whose underlying set is the complement of the image of $i_2$ on which $i_1$ restricts to an open immersion; (vii) a closed set $Z_0\subseteq\operatorname{Spec}R$ such that a geometric fibre is smooth precisely when its closed point lies off $Z_0$. Then for every scheme $T$, every $t\colon T\to\operatorname{Spec}R$ locally of finite type and every rigidified line bundle $L$ on $C\times_{\operatorname{Spec}R}T$ (an invertible module $L.L$ whose pullback along the section induced by $\varepsilon$ is isomorphic to the unit), there is an open $W\subseteq T$ whose intersection with $t^{-1}(Z_0)$ is exactly the set of $x\in T$ with $t(x)\in Z_0$ such that for every algebraically closed field $k$ and every $s\colon\operatorname{Spec}k\to T$ with image $\{x\}$, the restriction of $L.L$ to the fibre over $s$ satisfies `IsAlgEquivZero`, i.e. there are a scheme $T'$ locally of finite type and geometrically integral over $k$, an invertible module $M$ on the base change of the fibre to $T'$ and two $k$-sections $t_0,t_1$ of $T'$ such that the pullback of $M$ along $t_0$ is isomorphic to the structure sheaf and along $t_1$ to the restriction of $L.L$.
--
--   This is the openness, along the degeneration locus $t^{-1}(Z_0)$, of the locus of rigidified line bundles that are algebraically equivalent to zero on geometric fibres, for a proper flat pointed curve all of whose singular geometric fibres are transversal gluings of two coordinatised projective lines. It supplies the degeneration-stratum input to the two-strata openness statements for the relative Picard functor, being cited by [`AlgebraicGeometry.RelPicard.exists_opens_range_subset_iff_isAlgEquivZero_twistModule_baseChange_of_twoLineDegenerations`](thm.html#AlgebraicGeometry.RelPicard.exists_opens_range_subset_iff_isAlgEquivZero_twistModule_baseChange_of_twoLineDegenerations) and by [`AlgebraicGeometry.RelPicard.isLFPSurj_relSubPicPresheaf_algEquivZeroCut_baseChange_of_twoLineDegenerations`](thm.html#AlgebraicGeometry.RelPicard.isLFPSurj_relSubPicPresheaf_algEquivZeroCut_baseChange_of_twoLineDegenerations).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_isOpen_inter_preimage_eq_setOf_isAlgEquivZero_fibre_of_smoothLocus_of_twoLineDegenerations.lean

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
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian AlgebraicCurve

theorem AlgebraicGeometry.RelPicard.exists_isOpen_inter_preimage_eq_setOf_isAlgEquivZero_fibre_of_smoothLocus_of_twoLineDegenerations
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c] [Flat c]
    (𝒱 : C.TwoAffineOpenCover)
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))

    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (hε : Set.range ε.1.base ⊆ (U : Set C))

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

    (Z₀ : Set ↥(Spec (CommRingCat.of R))) (hZ₀ : IsClosed Z₀)
    (hZ₀off : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)),
      s.base (IsLocalRing.closedPoint k) ∉ Z₀ → Smooth (pullback.snd c s))
    (hZ₀on : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)),
      s.base (IsLocalRing.closedPoint k) ∈ Z₀ → ¬ Smooth (pullback.snd c s)) :
    ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
      (L : RigidifiedLineBundle c ε t), ∃ W : Set ↥T, IsOpen W ∧
        W ∩ (⇑t) ⁻¹' Z₀ = {x : ↥T | t x ∈ Z₀ ∧ ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T),
          Set.range ⇑s ⊆ {x} → IsAlgEquivZero (fibreAt c t s) (fibreModule c t s L.L)} := by sorry
