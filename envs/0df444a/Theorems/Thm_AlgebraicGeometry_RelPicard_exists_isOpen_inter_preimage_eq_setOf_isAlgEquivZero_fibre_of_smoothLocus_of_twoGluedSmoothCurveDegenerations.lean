-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_isOpen_inter_preimage_eq_setOf_isAlgEquivZero_fibre_of_smoothLocus_of_twoGluedSmoothCurveDegenerations
-- name    : AlgebraicGeometry.RelPicard.exists_isOpen_inter_preimage_eq_setOf_isAlgEquivZero_fibre_of_smoothLocus_of_twoGluedSmoothCurveDegenerations
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/1e368746-4f6b-55d5-bd1b-405d279dbc4f
-- title:
--   Relative openness of the Pic⁰ locus over a degeneration locus
-- statement:
--   Let $R$ be a Noetherian commutative ring and let $c : C \to \operatorname{Spec} R$ be proper and flat, equipped with a two-affine open cover $\mathcal V$ of $C$ (two affine opens with affine intersection whose union is $C$), and assume that for every $R$-algebra $A$ the structure map $A \to \Gamma(C \times_{\operatorname{Spec} R} \operatorname{Spec} A, \mathcal O)$, taken with respect to the second projection, is bijective. Let $U \subseteq C$ be an open subscheme whose composite $U \hookrightarrow C \to \operatorname{Spec} R$ is smooth of relative dimension $1$, and let $\varepsilon$ be a section of $c$ whose image lies in $U$. Assume: for every algebraically closed field $k$ and every $x : \operatorname{Spec} k \to \operatorname{Spec} R$ with smooth fibre, the whole fibre lies in $U$; every geometric fibre of $c$ is reduced; there is a fixed $g \in \mathbb N$ such that, for every geometric point and every two-affine open cover of the fibre (formed by base change along the identity of $\operatorname{Spec} R$), the two-chart Čech $H^1$ of the structure sheaf has $k$-dimension $g$; and, for every geometric point $s$ with non-smooth fibre $C_s$, there are proper smooth of relative dimension $1$ geometrically integral curves $C_1, C_2$ over $k$ and closed immersions $i_1, i_2$ into $C_s$ over $k$, and an $n \in \mathbb N$, such that $C_s$ is the union of the two images, the scheme $C_1 \times_{C_s} C_2$ is reduced with $\operatorname{card} = n > 0$, the point $\varepsilon(s)$ of $C_s$ (via `sectionFibrePoint`, evaluated at the closed point of $\operatorname{Spec} k$) lies in the image of $i_1$ but not of $i_2$, the preimage of $U$ in $C_s$ is the complement of the image of $C_1 \times_{C_s} C_2$, the image of $i_1$ meets this preimage in the connected component of $\varepsilon(s)$ there while the image of $i_2$ meets it in the complement of that component, and each $C_j$ restricted over the open complement of the other image immerses openly. Finally let $Z_0 \subseteq \operatorname{Spec} R$ be closed such that the geometric fibres over points outside $Z_0$ are smooth and those over points of $Z_0$ are not. Then for every scheme $T$, every $t : T \to \operatorname{Spec} R$ locally of finite type and every rigidified line bundle $L$ on $C \times_{\operatorname{Spec} R} T$ relative to $\varepsilon$ (an invertible module $L.L$ together with a trivialisation of its pullback along the rigidifying section), there exists an open $W \subseteq T$ with $W \cap t^{-1}(Z_0)$ equal to the set of $x \in T$ with $t(x) \in Z_0$ such that for every algebraically closed field $k$ and every $s : \operatorname{Spec} k \to T$ with set-theoretic image $\{x\}$ the restriction of $L.L$ to the fibre $C_s$ satisfies `IsAlgEquivZero`: there are a locally of finite type geometrically integral $h : T' \to \operatorname{Spec} k$, an invertible module $M$ on $C_s \times_{\operatorname{Spec} k} T'$ and two sections $t_0, t_1$ of $h$ such that the restriction of $M$ along $t_0$ is isomorphic to the structure sheaf and its restriction along $t_1$ is isomorphic to the given fibre bundle.
--
--   This is the relative openness statement for the locus where a rigidified line bundle on a proper flat curve lies in $\mathrm{Pic}^0$ (algebraic equivalence to zero on geometric fibres), in the case where the fibres over the degeneration locus $Z_0$ are unions of two smooth proper geometrically integral curves meeting in finitely many reduced points; the conclusion is openness relative to $t^{-1}(Z_0)$ only, the smooth stratum being handled separately. It feeds the construction of the open subscheme cutting out the $\mathrm{Pic}^0$ condition and the local finite presentation surjectivity of the relative sub-Picard presheaf for such degenerations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_isOpen_inter_preimage_eq_setOf_isAlgEquivZero_fibre_of_smoothLocus_of_twoGluedSmoothCurveDegenerations.lean

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
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian AlgebraicCurve

theorem AlgebraicGeometry.RelPicard.exists_isOpen_inter_preimage_eq_setOf_isAlgEquivZero_fibre_of_smoothLocus_of_twoGluedSmoothCurveDegenerations
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

    (Z₀ : Set ↥(Spec (CommRingCat.of R))) (hZ₀ : IsClosed Z₀)
    (hZ₀off : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)),
      s.base (IsLocalRing.closedPoint k) ∉ Z₀ → Smooth (pullback.snd c s))
    (hZ₀on : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)),
      s.base (IsLocalRing.closedPoint k) ∈ Z₀ → ¬ Smooth (pullback.snd c s)) :
    ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
      (L : RigidifiedLineBundle c ε t), ∃ W : Set ↥T, IsOpen W ∧
        W ∩ (⇑t) ⁻¹' Z₀ = {x : ↥T | t x ∈ Z₀ ∧ ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T),
          Set.range ⇑s ⊆ {x} → IsAlgEquivZero (fibreAt c t s) (fibreModule c t s L.L)} := by sorry
