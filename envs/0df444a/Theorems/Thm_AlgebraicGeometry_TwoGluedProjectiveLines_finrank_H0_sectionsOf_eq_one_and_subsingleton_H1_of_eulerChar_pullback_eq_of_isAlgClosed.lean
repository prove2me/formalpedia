-- Prove2me | Theorems.Thm_AlgebraicGeometry_TwoGluedProjectiveLines_finrank_H0_sectionsOf_eq_one_and_subsingleton_H1_of_eulerChar_pullback_eq_of_isAlgClosed
-- name    : AlgebraicGeometry.TwoGluedProjectiveLines.finrank_H0_sectionsOf_eq_one_and_subsingleton_H1_of_eulerChar_pullback_eq_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/cfa68e4c-cf39-50b4-8eb6-80ccbf14fcb1
-- title:
--   Multidegree (s-1,0) bundles on two glued lines: h⁰=1, H¹=0
-- statement:
--   Let $k$ be an algebraically closed field, $X$ a reduced scheme with a separated structure morphism $x \colon X \to \operatorname{Spec} k$, and let $M_1, M_2$ be curve models of $\mathrm{RatFunc}\,k$ over $k$: integral schemes, proper and smooth of relative dimension $1$ over $k$, with a fixed isomorphism of their function field with $k(T)$ compatible with $k$, a bijection `placeEquiv` between their closed points and the places of $k(T)/k$ matching stalks with valuation subrings, and every finite set of points contained in an affine open. Let $i_1 \colon M_1.C \to X$ and $i_2 \colon M_2.C \to X$ be closed immersions over $k$ (that is, $i_j$ followed by $x$ equals the structure morphism of $M_j$) whose images cover $X$. Let $s \in \mathbb{N}$ and $a, b \colon \mathrm{Fin}\,s \to k^\times$ with $a$ injective be such that, for each $i$, the point of $M_1.C$ corresponding to the place $T = a_i$ and the point of $M_2.C$ corresponding to $T = b_i$ have the same image in $X$, and such that these are the only coincidences: if $i_1(p) = i_2(q)$ then $p$ and $q$ are the points attached to $a_i$ and $b_i$ for some $i$. Assume the scheme-theoretic intersection $\mathrm{pullback}\,i_1\,i_2$ is reduced. Let $\mathcal{W}_0$ be a two-affine open cover of $X$ (two affine opens $U_0, U_1$ with affine intersection and union $\top$) whose traces are the standard charts: $i_j^{-1}U_0$ is the complement of the point at infinity of $M_j.C$ and $i_j^{-1}U_1$ the complement of the point $T = 0$, for $j = 1, 2$. Let $L$ be a module on $X$ which is invertible, i.e. every point has an open neighbourhood $U$ on which the restriction of $L$ is isomorphic to the unit module of $U$. Assume $i_2^{*}L$ is isomorphic to $i_2^{*}$ of the unit module of $X$, and that for every two-affine open cover $\mathcal{W}'$ of $M_1.C$ the difference $\dim_k H^0 - \dim_k H^1$ of the associated two-chart Čech complex of $i_1^{*}L$ equals $s$. Then for every two-affine open cover $\mathcal{W}$ of $X$ the space $H^0$ of the two-chart Čech complex of $L$ (the kernel of the difference of the two restriction maps into sections over $U_0 \cap U_1$) has $k$-dimension $1$, and the corresponding $H^1$ (the quotient of sections over $U_0 \cap U_1$ by the image of that difference) is trivial.
--
--   This is the interpolation statement for line bundles of multidegree $(s-1,0)$ on a union of two rational curves meeting transversally at $s$ points, as occurs in the fibre of the Deligne–Rapoport model at a point of bad reduction: such a bundle has a one-dimensional space of global sections and vanishing first cohomology, independently of the chosen two-chart cover. It is used in the construction of charts on the relative Picard scheme, notably by [`AlgebraicGeometry.RelPicard.subsingleton_H1_and_finrank_H0_fibre_of_twoGluedProjectiveLines`](thm.html#AlgebraicGeometry.RelPicard.subsingleton_H1_and_finrank_H0_fibre_of_twoGluedProjectiveLines) and the degeneration lemmas accompanying it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_TwoGluedProjectiveLines_finrank_H0_sectionsOf_eq_one_and_subsingleton_H1_of_eulerChar_pullback_eq_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicCurve

universe u

theorem AlgebraicGeometry.TwoGluedProjectiveLines.finrank_H0_sectionsOf_eq_one_and_subsingleton_H1_of_eulerChar_pullback_eq_of_isAlgClosed
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
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    [IsSeparated x]

    (hL₂ : Nonempty ((Scheme.Modules.pullback i₂).obj L ≅
        (Scheme.Modules.pullback i₂).obj (SheafOfModules.unit X.ringCatSheaf)))

    (hL₁ : ∀ 𝒲' : M₁.C.TwoAffineOpenCover,
      (Module.finrank k ↥(𝒲'.sectionsOf M₁.toBase ((Scheme.Modules.pullback i₁).obj L)).H0 : ℤ) -
        Module.finrank k (𝒲'.sectionsOf M₁.toBase ((Scheme.Modules.pullback i₁).obj L)).H1 = s) :
    ∀ 𝒲 : X.TwoAffineOpenCover,
      Module.finrank k ↥(𝒲.sectionsOf x L).H0 = 1 ∧ Subsingleton (𝒲.sectionsOf x L).H1 := by sorry
