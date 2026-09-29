-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_relEffCartierDiv_I_eq_zeroSchemeIdeal_chartModule_fibre
-- name    : AlgebraicGeometry.RelPicard.exists_relEffCartierDiv_I_eq_zeroSchemeIdeal_chartModule_fibre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/d0ac369d-c43e-5bc5-8d31-5607c5c73c81
-- title:
--   Fibrewise zero schemes as degree-g divisors inside U
-- statement:
--   Let $R$ be a Noetherian commutative ring and $c : C \to \operatorname{Spec} R$ a proper flat morphism of schemes, equipped with a two-chart affine open cover $\mathcal V$ of $C$, an open $U \subseteq C$ such that $U \hookrightarrow C$ followed by $c$ is smooth of relative dimension $1$, and a section $\varepsilon$ of $c$ (a morphism $\operatorname{Spec} R \to C$ composing with $c$ to the identity) whose image lies in $U$. Let $g, e, r$ be natural numbers with $g + e = r$, and let $D\gamma$ be a relative effective Cartier divisor of degree $e$ for $c$ over the identity of $\operatorname{Spec} R$ (an ideal sheaf datum on $C$ whose closed subscheme is finite, flat and locally of finite presentation over $\operatorname{Spec} R$ with all fibre ranks $e$), whose support lies in the preimage of $U$. The hypotheses are: for every algebraically closed field $k$, every $k$-point $x$ of $\operatorname{Spec} R$ and every two-chart affine cover $\mathcal W$ of the fibre, the two-term Čech complex of the fibre restriction of $\mathrm{sectionTwist}\ r \otimes D\gamma.\mathrm{idealModule}$ — where `sectionTwist` is the dual of the $r$-th power of the ideal of the rigidifying section — has $\dim_k H^0 - \dim_k H^1 = 1$, while the unit sheaf has $\dim_k H^1 = g$; whenever a geometric fibre $\mathrm{pullback.snd}\ c\ x$ is smooth, its image in $C$ lies in $U$ and it is geometrically irreducible; every geometric fibre $\mathrm{pullback}\ c\ x$ is reduced; for every non-smooth geometric fibre, a two-line degeneration package (summarised here) provides two curve models over $k$ with function field $\mathrm{RatFunc}\ k$, closed immersions of them onto the fibre over $k$ covering it, a finite list of pairwise identifications of their rational points given by injective $a$ and by $b$ with values in $k^\times$, reducedness of the fibre product of the two immersions, a prescribed two-chart cover pulling back to the complements of $\infty$ and of $0$ on each model, the matching of $i_1(\infty)$ with the point cut out by $\varepsilon$, the identification of the part of the first line inside the preimage of $U$ with the connected component of the $\varepsilon$-point, the statement that the preimage of $U$ is exactly the complement of the identified points, and an open subset of the fibre whose underlying set is the complement of the second line's image on which the first immersion is an open immersion; and finally, for every non-smooth geometric fibre, the preimage of the image of the subscheme of $D\gamma$ lies in that same connected component of the $\varepsilon$-point. Under these hypotheses the conclusion is: for every scheme $T$ with a morphism $t : T \to \operatorname{Spec} R$ locally of finite type, every rigidified line bundle $L$ for $c$, $\varepsilon$ over $t$ satisfying `FibrewiseAlgEquivZero`, every algebraically closed field $k$, every $x : \operatorname{Spec} k \to T$ and every nonzero morphism $\sigma$ from the unit module to the pullback along $\mathrm{mapOnProdOver}\ c\ x$ of $L.L \otimes (\mathrm{sectionTwist}\ c\ \varepsilon\ t\ r \otimes (D\gamma\ \text{pulled back along}\ t).\mathrm{idealModule})$, there is a relative effective Cartier divisor $D_x$ of degree $g$ for $c$ over $x \circ t$ whose ideal sheaf datum equals `Scheme.Modules.zeroSchemeIdeal σ` (the least ideal sheaf datum dominating the coefficient ideals of $\sigma$ on all affine opens) and whose support lies in the preimage of $U$.
--
--   This is the fibrewise zero-scheme statement for the theta-type bundle $L \otimes \mathcal O(r\varepsilon) \otimes \mathcal I_{D\gamma}$: a nonzero section on a geometric fibre cuts out an effective Cartier divisor of degree $g$ lying in the smooth chart $U$. It is the hypothesis consumed by the construction of open charts of the relative Picard functor for semistable families, used downstream in [`AlgebraicGeometry.RelPicard.forall_prime_exists_representsRelSubPic_algEquivZeroCut_baseChange_away_of_smoothLocus_of_twoLineDegenerations`](thm.html#AlgebraicGeometry.RelPicard.forall_prime_exists_representsRelSubPic_algEquivZeroCut_baseChange_away_of_smoothLocus_of_twoLineDegenerations).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_relEffCartierDiv_I_eq_zeroSchemeIdeal_chartModule_fibre.lean

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

theorem AlgebraicGeometry.RelPicard.exists_relEffCartierDiv_I_eq_zeroSchemeIdeal_chartModule_fibre
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [Flat c] (𝒱 : C.TwoAffineOpenCover) (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (hεU : Set.range ε.1 ⊆ (U : Set C))
    (g e r : ℕ) (hr : g + e = r)
    (Dγ : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R)))) (hDγU : Dγ.SupportedIn U)

    (hχ : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover),
      (Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) r ⊗ Dγ.idealModule))).H0 : ℤ) -
        Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) r ⊗ Dγ.idealModule))).H1 = 1)

    (hg : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover),
      Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
        (SheafOfModules.unit (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).ringCatSheaf)).H1 = g)

    (hgoodU : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)),
      Smooth (pullback.snd c x) → Set.range (pullback.fst c x).base ⊆ (U : Set C))
    (hgoodirr : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)),
      Smooth (pullback.snd c x) → GeometricallyIrreducible (pullback.snd c x))
    (hgred : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)), IsReduced (pullback c x))

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

    (hDγcomp : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)),
      ¬ Smooth (pullback.snd c s) →
      (pullback.fst c s).base ⁻¹' ((Dγ.I.subschemeι ≫ pullback.fst c (𝟙 _)).base '' Set.univ) ⊆
        connectedComponentIn ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s))
          (((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k)))
    :
    ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
      (L : RigidifiedLineBundle c ε t), FibrewiseAlgEquivZero L →
      ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ T)
        (σ : 𝟙_ (pullback c (x ≫ t)).Modules ⟶ (Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule))), σ ≠ 0 →
        ∃ Dx : RelEffCartierDiv c g (x ≫ t), Dx.I = Scheme.Modules.zeroSchemeIdeal σ ∧ Dx.SupportedIn U := by sorry
