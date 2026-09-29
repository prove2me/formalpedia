-- Prove2me | Theorems.Thm_AlgebraicGeometry_TwoGluedProjectiveLines_nonempty_iso_unit_of_isAlgEquivZero_of_ne_zero
-- name    : AlgebraicGeometry.TwoGluedProjectiveLines.nonempty_iso_unit_of_isAlgEquivZero_of_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/0b146cbb-c122-50c5-8287-acba13859402
-- title:
--   Algebraically trivial bundle with a section on two glued lines
-- statement:
--   Let $k$ be an algebraically closed field, $X$ a reduced scheme with a morphism $x : X \to \operatorname{Spec} k$, and let $M_1, M_2$ be curve models of $k(t)$ over $k$: integral schemes $M_i.C$, proper and smooth of relative dimension $1$ over $\operatorname{Spec} k$, equipped with an isomorphism of $k(t)$ onto the function field compatible with the structure map, a bijection `placeEquiv` from the closed points onto the places of $k(t)/k$ matching stalks with valuation subrings, and such that every finite set of points lies in an affine open. Assume given closed immersions $i_1 : M_1.C \to X$, $i_2 : M_2.C \to X$ over $\operatorname{Spec} k$ whose images cover $X$, units $a, b : \mathrm{Fin}\,s \to k^\times$ with $a$ injective, such that for each $i$ the point of $M_1.C$ at the place $t = a_i$ and the point of $M_2.C$ at the place $t = b_i$ have the same image in $X$, and such that every coincidence $i_1(p) = i_2(q)$ is of this form; assume further that the scheme-theoretic intersection $\mathrm{pullback}\ i_1\ i_2$ is reduced. Let $\mathcal W_0$ be a two-affine open cover of $X$ (affine opens $U_0, U_1$ with $U_0 \sqcup U_1 = \top$ and $U_0 \cap U_1$ affine) whose member $U_0$ pulls back on each line to the complement of the point at the infinite place, and whose member $U_1$ pulls back on each line to the complement of the point at $t = 0$. Let $L$ be an $\mathcal O_X$-module that is invertible, i.e. each point of $X$ has an open neighbourhood $U$ on which the restriction of $L$ is isomorphic to the unit module, and suppose `IsAlgEquivZero x L` holds: there are a $k$-scheme $h : T' \to \operatorname{Spec} k$ locally of finite type and geometrically integral, an invertible module $M$ on $X \times_k T'$, and two sections $t_0, t_1$ of $h$ over $\operatorname{Spec} k$ such that the pullback of $M$ along the base change of $t_0$ is isomorphic to the unit module of $X \times_k \operatorname{Spec} k$, while its pullback along the base change of $t_1$ is isomorphic to the pullback of $L$ to $X \times_k \operatorname{Spec} k$. Finally let $\sigma$ be a nonzero morphism from the unit module of $X$ to $L$. Then $L$ is isomorphic to the unit module $\mathcal O_X$.
--
--   This is the fibrewise triviality hypothesis ("an algebraically trivial invertible module with a nonzero global section on a geometric fibre is trivial") required by the representability theorem for the $\mathrm{Pic}^0$ cut of the relative Picard functor, verified here for the degenerate fibre consisting of two projective lines glued transversally at $s$ points. It feeds [`ModularCurve.nonempty_legTwoInputV2`](thm.html#ModularCurve.nonempty_legTwoInputV2), and is established by comparing the Čech Euler characteristics of $L$ and of $\mathcal O_X$ computed on $\mathcal W_0$ via the explicit glued-lines complexes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_TwoGluedProjectiveLines_nonempty_iso_unit_of_isAlgEquivZero_of_ne_zero.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_TwoChartCech_GluedLines
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.RelPicard

universe u

theorem AlgebraicGeometry.TwoGluedProjectiveLines.nonempty_iso_unit_of_isAlgEquivZero_of_ne_zero
    (k : Type u) [Field k] [IsAlgClosed k] [DecidableEq (RatFunc k)]
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
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) (h0 : IsAlgEquivZero x L)
    (σ : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ L) (hσ : σ ≠ 0) :
    Nonempty (L ≅ SheafOfModules.unit X.ringCatSheaf) := by sorry
