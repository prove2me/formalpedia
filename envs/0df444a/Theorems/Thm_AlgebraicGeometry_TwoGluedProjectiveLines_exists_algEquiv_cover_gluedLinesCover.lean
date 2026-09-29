-- Prove2me | Theorems.Thm_AlgebraicGeometry_TwoGluedProjectiveLines_exists_algEquiv_cover_gluedLinesCover
-- name    : AlgebraicGeometry.TwoGluedProjectiveLines.exists_algEquiv_cover_gluedLinesCover
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/67d7d06c-c4bf-558b-aaad-fa0a03e10378
-- title:
--   Chart rings of two projective lines glued at nodes
-- statement:
--   Let $k$ be a field, $X$ a reduced scheme with a morphism $x : X \to \operatorname{Spec} k$, and let $M_1, M_2$ be curve models of $k(T)$ over $k$: each consists of an integral scheme $C$, proper and smooth of relative dimension $1$ over $\operatorname{Spec} k$, together with a ring isomorphism $k(T) \cong$ the function field of $C$ compatible with the structure morphism, a bijection between the closed points of $C$ and the places of $k(T)/k$ (valuation subrings containing $k$, different from $k(T)$, principal ideal rings) matching stalks with valuation rings, and the property that every finite set of points lies in one affine open. Assume given closed immersions $i_1 : M_1.C \to X$, $i_2 : M_2.C \to X$ over $\operatorname{Spec} k$ (i.e. $i_j$ followed by $x$ is the structure morphism of $M_j$) whose images cover $X$ as a set; an integer $s$ and units $a, b : \mathrm{Fin}\,s \to k^\times$ with $a$ injective; for each $i$, the closed point of $M_1.C$ attached to the place of $T - a_i$ and the closed point of $M_2.C$ attached to the place of $T - b_i$ have the same image in $X$; conversely any pair of points of $M_1.C$, $M_2.C$ with equal image in $X$ is of this shape; the fibre product $M_1.C \times_X M_2.C$ is reduced; and a two-chart affine cover $\mathcal{W}_0$ of $X$ (affine opens $U_0, U_1$ with $U_0 \sqcup U_1 = \top$ and $U_0 \cap U_1$ affine) such that, in both models, the preimage of $U_0$ is the complement of the point attached to the place at infinity and the preimage of $U_1$ is the complement of the point attached to the place of $T$. Then there are $k$-algebra isomorphisms $\Gamma(X, U_0) \cong A_0$, $\Gamma(X, U_1) \cong A_1$, $\Gamma(X, U_0 \cap U_1) \cong A_{01}$, where $A_{01}$ is the subalgebra `gluedLinesOverlap k a b` of $k[T, T^{-1}] \times k[T, T^{-1}]$ recording the node conditions attached to $a$ and $b$, $A_0$ is its intersection with the product of two copies of `polyPart k` (Laurent polynomials supported in non-negative exponents) and $A_1$ its intersection with the product of two copies of `invPolyPart k`, and these three isomorphisms commute with the two restriction maps $\Gamma(X,U_j) \to \Gamma(X, U_0 \cap U_1)$ on the one side and the subalgebra inclusions on the other. The isomorphisms are asserted only to exist; no normalisation relative to the coordinate $T$ is claimed.
--
--   This is the identification of the two-chart Čech data of a curve obtained by gluing two smooth proper models of $k(T)$ transversally at the labelled points $a_i \sim b_i$ with the explicit algebra of pairs of (Laurent) polynomials agreeing at the nodes. It feeds the computation of Čech sections and of the Euler characteristic of such a glued curve over an algebraically closed field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_TwoGluedProjectiveLines_exists_algEquiv_cover_gluedLinesCover.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_TwoChartCech_GluedLines

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

universe u

theorem AlgebraicGeometry.TwoGluedProjectiveLines.exists_algEquiv_cover_gluedLinesCover
    (k : Type u) [Field k] [DecidableEq (RatFunc k)]
    {X : Scheme.{u}} (x : X ⟶ Spec (.of k)) [IsReduced X]
    (M₁ M₂ : CurveModel k (RatFunc k)) (i₁ : M₁.C ⟶ X) (i₂ : M₂.C ⟶ X)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (hi₁ : i₁ ≫ x = M₁.toBase) (hi₂ : i₂ ≫ x = M₂.toBase)
    (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    {s : ℕ} (a b : Fin s → kˣ) (ha : Function.Injective a)
    (hnode : ∀ i, i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 =
      i₂.base (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k (b i : k))).1)
    (hinter : ∀ (p : M₁.C) (q : M₂.C), i₁.base p = i₂.base q →
      ∃ i, p = (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 ∧
        q = (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k (b i : k))).1)
    (htrans : IsReduced (pullback i₁ i₂))
    (𝒲₀ : X.TwoAffineOpenCover)
    (hU0₁ : ((i₁ ⁻¹ᵁ 𝒲₀.U0 : M₁.C.Opens) : Set M₁.C) =
      {(M₁.placeEquiv.symm (RationalFunctionField.placeInfty k)).1}ᶜ)
    (hU0₂ : ((i₂ ⁻¹ᵁ 𝒲₀.U0 : M₂.C.Opens) : Set M₂.C) =
      {(M₂.placeEquiv.symm (RationalFunctionField.placeInfty k)).1}ᶜ)
    (hU1₁ : ((i₁ ⁻¹ᵁ 𝒲₀.U1 : M₁.C.Opens) : Set M₁.C) =
      {(M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k 0)).1}ᶜ)
    (hU1₂ : ((i₂ ⁻¹ᵁ 𝒲₀.U1 : M₂.C.Opens) : Set M₂.C) =
      {(M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k 0)).1}ᶜ)
 :
    ∃ (φ₀ : (𝒲₀.cover x).A0 ≃ₐ[k] (TwoChartCech.gluedLinesCover k a b).A0)
      (φ₁ : (𝒲₀.cover x).A1 ≃ₐ[k] (TwoChartCech.gluedLinesCover k a b).A1)
      (φ₀₁ : (𝒲₀.cover x).A01 ≃ₐ[k] (TwoChartCech.gluedLinesCover k a b).A01),
      (∀ f, φ₀₁ ((𝒲₀.cover x).ρ0 f) = (TwoChartCech.gluedLinesCover k a b).ρ0 (φ₀ f)) ∧
      (∀ f, φ₀₁ ((𝒲₀.cover x).ρ1 f) = (TwoChartCech.gluedLinesCover k a b).ρ1 (φ₁ f)) := by sorry
