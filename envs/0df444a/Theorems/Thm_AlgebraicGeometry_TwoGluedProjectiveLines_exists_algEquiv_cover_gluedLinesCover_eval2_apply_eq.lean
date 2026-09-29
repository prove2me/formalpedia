-- Prove2me | Theorems.Thm_AlgebraicGeometry_TwoGluedProjectiveLines_exists_algEquiv_cover_gluedLinesCover_eval2_apply_eq
-- name    : AlgebraicGeometry.TwoGluedProjectiveLines.exists_algEquiv_cover_gluedLinesCover_eval2_apply_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/be9048cc-952f-55d5-b191-30166433c5eb
-- title:
--   Anchored chart dictionary for two transversally glued projective lines
-- statement:
--   Let $k$ be a field, $X$ a reduced scheme with a morphism $x : X \to \operatorname{Spec} k$, and let $M_1, M_2$ be curve models of $k(T)$ over $k$: each consists of an integral scheme $C$, proper and smooth of relative dimension $1$ over $\operatorname{Spec} k$, a ring isomorphism of $\mathrm{RatFunc}\,k$ with the function field of $C$ compatible with the structural map from $k$, a bijection `placeOfPoint` from the closed points of $C$ onto the places of $k(T)/k$ whose stalks have the prescribed valuation subrings as images in $k(T)$, and the property that every finite set of points lies in an affine open. Let $i_1 : M_1.C \to X$, $i_2 : M_2.C \to X$ be closed immersions with $i_1 \circ x = M_1.\mathrm{toBase}$, $i_2 \circ x = M_2.\mathrm{toBase}$, whose images cover $X$; let $a, b : \mathrm{Fin}\,s \to k^\times$ with $a$ injective, such that for each $i$ the closed point of $M_1.C$ corresponding under `placeEquiv` to the place $\mathrm{placeOfPoint}\,a_i$ of $k(T)$ has the same image in $X$ as the point of $M_2.C$ at $\mathrm{placeOfPoint}\,b_i$, and such that every coincidence $i_1(p) = i_2(q)$ is of this form; assume the scheme-theoretic intersection $M_1.C \times_X M_2.C$ is reduced. Let $\mathcal{W}_0$ be a pair of affine opens $U_0, U_1$ of $X$ with $U_0 \sqcup U_1 = \top$ and $U_0 \cap U_1$ affine, such that in each $M_j.C$ the preimage of $U_0$ is the complement of the point at $\mathrm{placeInfty}$ and the preimage of $U_1$ is the complement of the point at $\mathrm{placeOfPoint}\,0$. The conclusion asserts the existence of isomorphisms of $k$-algebras $\varphi_0 : \Gamma(X, U_0) \to A_0$, $\varphi_1 : \Gamma(X, U_1) \to A_1$, $\varphi_{01} : \Gamma(X, U_0 \cap U_1) \to A_{01}$, where $A_{01}$ is the subalgebra `gluedLinesOverlap k a b` of $k[T;T^{-1}] \times k[T;T^{-1}]$, $A_0$ its intersection with the product of two copies of `polyPart` (Laurent polynomials supported in non-negative exponents) and $A_1$ its intersection with the product of two copies of `invPolyPart`, the two restriction maps of the Čech cover of $A_{01}$ being the inclusions; the $\varphi$'s commute with the restriction maps $\Gamma(X,U_0) \to \Gamma(X,U_0\cap U_1)$ and $\Gamma(X,U_1) \to \Gamma(X,U_0\cap U_1)$ on the one side and these inclusions on the other; and they are anchored, in the sense that for $U$ each of $U_0$, $U_1$, $U_0 \cap U_1$ and for every $f \in \Gamma(X,U)$, the image in $k(T)$ of the $j$-th component of $\varphi_U(f)$ under the evaluation $\mathrm{eval}_2$ sending $k$ into $k(T)$ by the structural map and $T$ to the unit $X \in k(T)$ equals the image of the pullback $i_j^* f \in \Gamma(M_j.C, i_j^{-1}U)$ in the function field of $M_j.C$, read in $k(T)$ through $M_j.\mathrm{ffEquiv}^{-1}$, for $j = 1, 2$; these three anchoring clauses are stated under non-emptiness assumptions on the traces of $U$ in $M_1.C$ and $M_2.C$.
--
--   This is the explicit dictionary identifying the structure sheaf of two projective lines glued transversally at $s$ labelled $k$-rational points with the combinatorially defined two-chart cover by glued Laurent-polynomial algebras, in the strengthened form in which the isomorphisms are pinned down by pullback to the two lines written in the coordinate $T$. It feeds the comparison of Čech sections and the Euler characteristic computation for such curves over an algebraically closed field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_TwoGluedProjectiveLines_exists_algEquiv_cover_gluedLinesCover_eval2_apply_eq.lean

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

theorem AlgebraicGeometry.TwoGluedProjectiveLines.exists_algEquiv_cover_gluedLinesCover_eval2_apply_eq
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
      (∀ f, φ₀₁ ((𝒲₀.cover x).ρ1 f) = (TwoChartCech.gluedLinesCover k a b).ρ1 (φ₁ f)) ∧
      (∀ [Nonempty (i₁ ⁻¹ᵁ 𝒲₀.U0 : M₁.C.Opens)] [Nonempty (i₂ ⁻¹ᵁ 𝒲₀.U0 : M₂.C.Opens)] (f : (𝒲₀.cover x).A0),
        LaurentPolynomial.eval₂ (algebraMap k (RatFunc k)) (Units.mk0 (RatFunc.X : RatFunc k) RatFunc.X_ne_zero)
            ((φ₀ f : (TwoChartCech.gluedLinesCover k a b).A0) : LaurentPolynomial k × LaurentPolynomial k).1 =
          ((M₁.ffEquiv.symm : M₁.C.functionField ≃+* RatFunc k).toRingHom.comp
            (algebraMap Γ(M₁.C, i₁ ⁻¹ᵁ 𝒲₀.U0) M₁.C.functionField)) ((i₁.app 𝒲₀.U0) f) ∧
        LaurentPolynomial.eval₂ (algebraMap k (RatFunc k)) (Units.mk0 (RatFunc.X : RatFunc k) RatFunc.X_ne_zero)
            ((φ₀ f : (TwoChartCech.gluedLinesCover k a b).A0) : LaurentPolynomial k × LaurentPolynomial k).2 =
          ((M₂.ffEquiv.symm : M₂.C.functionField ≃+* RatFunc k).toRingHom.comp
            (algebraMap Γ(M₂.C, i₂ ⁻¹ᵁ 𝒲₀.U0) M₂.C.functionField)) ((i₂.app 𝒲₀.U0) f)) ∧
      (∀ [Nonempty (i₁ ⁻¹ᵁ 𝒲₀.U1 : M₁.C.Opens)] [Nonempty (i₂ ⁻¹ᵁ 𝒲₀.U1 : M₂.C.Opens)] (f : (𝒲₀.cover x).A1),
        LaurentPolynomial.eval₂ (algebraMap k (RatFunc k)) (Units.mk0 (RatFunc.X : RatFunc k) RatFunc.X_ne_zero)
            ((φ₁ f : (TwoChartCech.gluedLinesCover k a b).A1) : LaurentPolynomial k × LaurentPolynomial k).1 =
          ((M₁.ffEquiv.symm : M₁.C.functionField ≃+* RatFunc k).toRingHom.comp
            (algebraMap Γ(M₁.C, i₁ ⁻¹ᵁ 𝒲₀.U1) M₁.C.functionField)) ((i₁.app 𝒲₀.U1) f) ∧
        LaurentPolynomial.eval₂ (algebraMap k (RatFunc k)) (Units.mk0 (RatFunc.X : RatFunc k) RatFunc.X_ne_zero)
            ((φ₁ f : (TwoChartCech.gluedLinesCover k a b).A1) : LaurentPolynomial k × LaurentPolynomial k).2 =
          ((M₂.ffEquiv.symm : M₂.C.functionField ≃+* RatFunc k).toRingHom.comp
            (algebraMap Γ(M₂.C, i₂ ⁻¹ᵁ 𝒲₀.U1) M₂.C.functionField)) ((i₂.app 𝒲₀.U1) f)) ∧
      (∀ [Nonempty (i₁ ⁻¹ᵁ (𝒲₀.U0 ⊓ 𝒲₀.U1) : M₁.C.Opens)] [Nonempty (i₂ ⁻¹ᵁ (𝒲₀.U0 ⊓ 𝒲₀.U1) : M₂.C.Opens)] (f : (𝒲₀.cover x).A01),
        LaurentPolynomial.eval₂ (algebraMap k (RatFunc k)) (Units.mk0 (RatFunc.X : RatFunc k) RatFunc.X_ne_zero)
            ((φ₀₁ f : (TwoChartCech.gluedLinesCover k a b).A01) : LaurentPolynomial k × LaurentPolynomial k).1 =
          ((M₁.ffEquiv.symm : M₁.C.functionField ≃+* RatFunc k).toRingHom.comp
            (algebraMap Γ(M₁.C, i₁ ⁻¹ᵁ (𝒲₀.U0 ⊓ 𝒲₀.U1)) M₁.C.functionField)) ((i₁.app (𝒲₀.U0 ⊓ 𝒲₀.U1)) f) ∧
        LaurentPolynomial.eval₂ (algebraMap k (RatFunc k)) (Units.mk0 (RatFunc.X : RatFunc k) RatFunc.X_ne_zero)
            ((φ₀₁ f : (TwoChartCech.gluedLinesCover k a b).A01) : LaurentPolynomial k × LaurentPolynomial k).2 =
          ((M₂.ffEquiv.symm : M₂.C.functionField ≃+* RatFunc k).toRingHom.comp
            (algebraMap Γ(M₂.C, i₂ ⁻¹ᵁ (𝒲₀.U0 ⊓ 𝒲₀.U1)) M₂.C.functionField)) ((i₂.app (𝒲₀.U0 ⊓ 𝒲₀.U1)) f)) := by sorry
