-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_twoGluedSmoothCurveDegeneration_of_factor_of_isAlgClosed
-- name    : AlgebraicGeometry.exists_twoGluedSmoothCurveDegeneration_of_factor_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/4fb12f72-bce1-5c1a-9e66-1bba8ee95374
-- title:
--   Two-component degenerate fibre persists under algebraically closed base extension
-- statement:
--   Let $R$ be a commutative ring, $c\colon C\to\operatorname{Spec}R$ a scheme over it, $U$ an open subscheme of $C$, and $\varepsilon$ a section of $c$, i.e. a morphism $\operatorname{Spec}R\to C$ composing with $c$ to the identity. Let $k_0$ be an algebraically closed field and $s_0\colon\operatorname{Spec}k_0\to\operatorname{Spec}R$, and assume the fibre $C\times_{\operatorname{Spec}R}\operatorname{Spec}k_0$ admits the following description: there are schemes $C_1,C_2$ with structure morphisms to $\operatorname{Spec}k_0$ that are proper, smooth of relative dimension $1$ and geometrically integral, morphisms $i_1,i_2$ from $C_1,C_2$ into the fibre commuting with the projections to $\operatorname{Spec}k_0$ and both closed immersions, and $n\in\mathbb N$, such that every point of the fibre lies in the image of $i_1$ or of $i_2$; $C_1\times_{\text{fibre}}C_2$ is reduced with exactly $n$ points and $n>0$; the image of the closed point under the induced section point $\varepsilon(s_0)$ of the fibre lies in the image of $i_1$ but not of $i_2$; the preimage of $U$ in the fibre is the complement of the image of the intersection $C_1\times_{\text{fibre}}C_2$; that preimage meets the image of $i_1$ in exactly the connected component of $\varepsilon(s_0)$ in it, and meets the image of $i_2$ in the rest of it; and there are open subschemes of the fibre with underlying sets the complements of the images of $i_2$, resp. $i_1$, whose pullbacks along $i_1$, resp. $i_2$, map by an open immersion into the fibre. Then for every algebraically closed field $k$, ring homomorphism $\iota\colon k_0\to k$ and $s\colon\operatorname{Spec}k\to\operatorname{Spec}R$ with $s=\operatorname{Spec}(\iota)$ followed by $s_0$, the fibre $C\times_{\operatorname{Spec}R}\operatorname{Spec}k$ admits a description of exactly the same shape (with its own $C_1,C_2,i_1,i_2$ and its own $n>0$).
--
--   This is the base-change stability of the geometric hypothesis describing a degenerate fibre as two smooth proper geometrically integral curves crossing transversally in finitely many points, with the section landing on the first component and the open subscheme $U$ cutting out the complement of the crossings: the description over one algebraically closed residue field propagates to every algebraically closed extension. It is used in [`ModularCurve.XHDRModelAtP.exists_twoGluedSmoothCurveDegeneration_of_not_smooth`](thm.html#ModularCurve.XHDRModelAtP.exists_twoGluedSmoothCurveDegeneration_of_not_smooth) to supply this hypothesis for arbitrary algebraically closed geometric points from a single one, in the analysis of the bad fibres of the modular curve models entering the relative Picard construction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_twoGluedSmoothCurveDegeneration_of_factor_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

theorem AlgebraicGeometry.exists_twoGluedSmoothCurveDegeneration_of_factor_of_isAlgClosed
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (U : C.Opens) (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    {k₀ : Type u} [Field k₀] [IsAlgClosed k₀] (s₀ : Spec (CommRingCat.of k₀) ⟶ Spec (CommRingCat.of R))
    (h₀ : ∃ (C₁ C₂ : Scheme.{u}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k₀)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k₀))
        (_ : IsProper c₁) (_ : SmoothOfRelativeDimension 1 c₁) (_ : GeometricallyIntegral c₁)
        (_ : IsProper c₂) (_ : SmoothOfRelativeDimension 1 c₂) (_ : GeometricallyIntegral c₂)
        (i₁ : SchemeHomOver c₁ (pullback.snd c s₀)) (i₂ : SchemeHomOver c₂ (pullback.snd c s₀))
        (_ : IsClosedImmersion i₁.1) (_ : IsClosedImmersion i₂.1) (n : ℕ),
        (∀ z : ↥(pullback c s₀), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base) ∧
        IsReduced (pullback i₁.1 i₂.1) ∧ Nat.card ↥(pullback i₁.1 i₂.1) = n ∧ 0 < n ∧
        ((sectionFibrePoint ε s₀).1).base (IsLocalRing.closedPoint k₀) ∈ Set.range i₁.1.base \ Set.range i₂.1.base ∧
        ((pullback.fst c s₀ ⁻¹ᵁ U : (pullback c s₀).Opens) : Set ↥(pullback c s₀)) =
          (Set.range (pullback.fst i₁.1 i₂.1 ≫ i₁.1).base)ᶜ ∧
        Set.range i₁.1.base ∩ ((pullback.fst c s₀ ⁻¹ᵁ U : (pullback c s₀).Opens) : Set ↥(pullback c s₀)) =
          connectedComponentIn ((pullback.fst c s₀ ⁻¹ᵁ U : (pullback c s₀).Opens) : Set ↥(pullback c s₀))
            (((sectionFibrePoint ε s₀).1).base (IsLocalRing.closedPoint k₀)) ∧
        Set.range i₂.1.base ∩ ((pullback.fst c s₀ ⁻¹ᵁ U : (pullback c s₀).Opens) : Set ↥(pullback c s₀)) =
          ((pullback.fst c s₀ ⁻¹ᵁ U : (pullback c s₀).Opens) : Set ↥(pullback c s₀)) \
            connectedComponentIn ((pullback.fst c s₀ ⁻¹ᵁ U : (pullback c s₀).Opens) : Set ↥(pullback c s₀))
              (((sectionFibrePoint ε s₀).1).base (IsLocalRing.closedPoint k₀)) ∧
        (∃ W₁ : (pullback c s₀).Opens, (W₁ : Set ↥(pullback c s₀)) = (Set.range i₂.1.base)ᶜ ∧
          IsOpenImmersion ((i₁.1 ⁻¹ᵁ W₁).ι ≫ i₁.1)) ∧
        (∃ W₂ : (pullback c s₀).Opens, (W₂ : Set ↥(pullback c s₀)) = (Set.range i₁.1.base)ᶜ ∧
          IsOpenImmersion ((i₂.1 ⁻¹ᵁ W₂).ι ≫ i₂.1)))
    {k : Type u} [Field k] [IsAlgClosed k] (ι : k₀ →+* k)
    (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) (hs : s = Spec.map (CommRingCat.ofHom ι) ≫ s₀) :
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
          IsOpenImmersion ((i₂.1 ⁻¹ᵁ W₂).ι ≫ i₂.1)) := by sorry
