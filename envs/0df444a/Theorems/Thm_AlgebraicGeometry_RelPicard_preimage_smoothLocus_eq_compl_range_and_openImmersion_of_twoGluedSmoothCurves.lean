-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_preimage_smoothLocus_eq_compl_range_and_openImmersion_of_twoGluedSmoothCurves
-- name    : AlgebraicGeometry.RelPicard.preimage_smoothLocus_eq_compl_range_and_openImmersion_of_twoGluedSmoothCurves
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/83f3062b-9264-553d-914c-3fcf03f4dafd
-- title:
--   Trace of the smooth locus on a two-component degenerate fibre
-- statement:
--   Let $R$ be a commutative ring and $c\colon C\to\operatorname{Spec}R$ a flat morphism, locally of finite presentation, and let $U\subseteq C$ be an open subscheme such that $U\hookrightarrow C$ followed by $c$ is smooth and such that every open $W\subseteq C$ with $W\hookrightarrow C$ followed by $c$ smooth satisfies $W\le U$. Let $k$ be an algebraically closed field, $s\colon\operatorname{Spec}k\to\operatorname{Spec}R$ a morphism, and assume the fibre $X=C\times_{\operatorname{Spec}R}\operatorname{Spec}k$ is reduced. Let $c_1\colon C_1\to\operatorname{Spec}k$ and $c_2\colon C_2\to\operatorname{Spec}k$ be proper, smooth of relative dimension $1$ and geometrically integral, and for $j=1,2$ let $i_j$ be a morphism $C_j\to X$ with $i_j$ followed by $\mathrm{pr}_2\colon X\to\operatorname{Spec}k$ equal to $c_j$, each a closed immersion. Assume every point of $X$ lies in the image of $i_1$ or of $i_2$, that neither image is contained in the other, and fix $p$ in the image of $i_1$ lying in $X_U:=\mathrm{pr}_1^{-1}(U)$. Then, as subsets of $X$: $X_U$ is the complement of the image of $C_1\times_X C_2\to C_1\to X$; $i_1(C_1)\cap X_U$ is the connected component of $p$ in $X_U$; $i_2(C_2)\cap X_U$ is $X_U$ minus that component; and there are opens $W_1,W_2\subseteq X$ with underlying sets the complements of $i_2(C_2)$ and of $i_1(C_1)$ such that $i_1^{-1}(W_1)\hookrightarrow C_1$ followed by $i_1$, and $i_2^{-1}(W_2)\hookrightarrow C_2$ followed by $i_2$, are open immersions.
--
--   This is the structural analysis of a degenerate fibre of a flat family that is the union of two smooth proper geometrically integral curves: the trace of the smooth locus of the family is exactly the complement of the crossing locus, the two punctured components are its connected components, and each component maps by an open immersion away from the other. It is used in the construction of models of modular curves, where the fibre at a bad prime has two such components.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_preimage_smoothLocus_eq_compl_range_and_openImmersion_of_twoGluedSmoothCurves.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

theorem AlgebraicGeometry.RelPicard.preimage_smoothLocus_eq_compl_range_and_openImmersion_of_twoGluedSmoothCurves
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [Flat c] [LocallyOfFinitePresentation c]
    (U : C.Opens) [Smooth (U.ι ≫ c)] (hUmax : ∀ W : C.Opens, Smooth (W.ι ≫ c) → W ≤ U)
    {k : Type u} [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (hXred : IsReduced (pullback c s))
    {C₁ C₂ : Scheme.{u}} (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ (pullback.snd c s)) (i₂ : SchemeHomOver c₂ (pullback.snd c s))
    [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hjs : ∀ z : ↥(pullback c s), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hne₁ : ¬ Set.range i₁.1.base ⊆ Set.range i₂.1.base) (hne₂ : ¬ Set.range i₂.1.base ⊆ Set.range i₁.1.base)
    (p : ↥(pullback c s)) (hp : p ∈ Set.range i₁.1.base)
    (hpU : p ∈ ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s))) :
    ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) =
      (Set.range (pullback.fst i₁.1 i₂.1 ≫ i₁.1).base)ᶜ ∧
    Set.range i₁.1.base ∩ ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) =
      connectedComponentIn ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) p ∧
    Set.range i₂.1.base ∩ ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) =
      ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) \
        connectedComponentIn ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) p ∧
    (∃ W₁ : (pullback c s).Opens, (W₁ : Set ↥(pullback c s)) = (Set.range i₂.1.base)ᶜ ∧
      IsOpenImmersion ((i₁.1 ⁻¹ᵁ W₁).ι ≫ i₁.1)) ∧
    (∃ W₂ : (pullback c s).Opens, (W₂ : Set ↥(pullback c s)) = (Set.range i₁.1.base)ᶜ ∧
      IsOpenImmersion ((i₂.1 ⁻¹ᵁ W₂).ι ≫ i₂.1)) := by sorry
