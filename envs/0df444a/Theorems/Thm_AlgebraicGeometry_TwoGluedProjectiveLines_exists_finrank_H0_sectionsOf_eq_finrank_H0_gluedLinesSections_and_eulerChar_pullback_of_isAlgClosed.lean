-- Prove2me | Theorems.Thm_AlgebraicGeometry_TwoGluedProjectiveLines_exists_finrank_H0_sectionsOf_eq_finrank_H0_gluedLinesSections_and_eulerChar_pullback_of_isAlgClosed
-- name    : AlgebraicGeometry.TwoGluedProjectiveLines.exists_finrank_H0_sectionsOf_eq_finrank_H0_gluedLinesSections_and_eulerChar_pullback_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/0d4f7b7b-32f6-5d10-bb8c-74ff2c08e281
-- title:
--   Čech cohomology of a bundle on two glued projective lines
-- statement:
--   Let $k$ be an algebraically closed field, let $X$ be a reduced scheme with a morphism $x\colon X\to\operatorname{Spec} k$, and let $M_1,M_2$ be curve models of $\operatorname{RatFunc} k$ over $k$, i.e. integral schemes $M_j.C$, proper and smooth of relative dimension $1$ over $\operatorname{Spec} k$, together with an isomorphism of $k(T)$ onto the function field and a bijection `placeEquiv` from the closed points onto the places of $k(T)/k$ matching stalks with valuation subrings. Let $i_1\colon M_1.C\to X$ and $i_2\colon M_2.C\to X$ be closed immersions with $i_j$ followed by $x$ equal to $M_j.toBase$, whose images cover $X$ set-theoretically. Let $a,b\colon \mathrm{Fin}\,s\to k^\times$ with $a$ injective, and assume: the closed point of $M_1.C$ corresponding to the place of $T-a_i$ and the point of $M_2.C$ corresponding to the place of $T-b_i$ have the same image under $i_1,i_2$ for every $i$; conversely any pair of points of $M_1.C$, $M_2.C$ with equal images arises from some index $i$ in this way; and the scheme $\operatorname{pullback} i_1\, i_2$ is reduced. Let $\mathcal W_0$ consist of two affine opens $U_0,U_1$ of $X$ with affine intersection and $U_0\sqcup U_1=\top$, whose preimages in $M_j.C$ are the complements of the point at the place $\infty$ (for $U_0$) and of the point at the place of $T$ (for $U_1$). Let $L$ be an $X$-module which is invertible in the sense that each point of $X$ has an open neighbourhood $U$ with the pullback of $L$ to $U$ isomorphic to the unit sheaf of modules. Then there are integers $n,m$ and $\lambda\colon \mathrm{Fin}\,s\to k^\times$ such that: the $k$-dimension of $H^0$ of the two-chart Čech data $\mathcal W_0.\mathrm{sectionsOf}\,x\,L$ (the kernel of the Čech difference map on $\Gamma(L,U_0)\times\Gamma(L,U_1)$) equals that of $H^0$ of the explicit glued-lines data [`TwoChartCech.gluedLinesSections k a b lam n m`](def/TwoChartCech_GluedLines.html#L126); the corresponding $H^1$ groups (cokernels of the Čech difference maps) are subsingleton simultaneously; $L$ is isomorphic to the unit sheaf of modules precisely when $n=0$, $m=0$ and $\lambda$ is constant; the pullback of $L$ along $i_1$ is isomorphic to the pullback of the unit sheaf precisely when $n=0$, and likewise along $i_2$ precisely when $m=0$; and for every two-affine-open cover $\mathcal W'$ of $M_1.C$ the difference $\dim_k H^0-\dim_k H^1$ of the Čech data of $i_1^*L$ equals $n+1$, and correspondingly $m+1$ on $M_2.C$.
--
--   This is the dictionary between a curve over an algebraically closed field consisting of two projective lines meeting transversally at $s$ rational points — the shape of the geometric special fibre of the Deligne–Rapoport model of $X_0(p)$, with the $j$-lines glued at the supersingular points — and the explicit Laurent-polynomial two-chart model of line bundles on it, recording the bidegree $(n,m)$ and the gluing parameters $\lambda$. It is used to compute $H^0$ and the vanishing of $H^1$ for invertible sheaves on such a fibre, and to characterise triviality of a bundle and of its restrictions to the two components.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_TwoGluedProjectiveLines_exists_finrank_H0_sectionsOf_eq_finrank_H0_gluedLinesSections_and_eulerChar_pullback_of_isAlgClosed.lean

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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicCurve

universe u

theorem AlgebraicGeometry.TwoGluedProjectiveLines.exists_finrank_H0_sectionsOf_eq_finrank_H0_gluedLinesSections_and_eulerChar_pullback_of_isAlgClosed
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
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) :
    ∃ (n m : ℤ) (lam : Fin s → kˣ),
      Module.finrank k ↥(𝒲₀.sectionsOf x L).H0 =
          Module.finrank k ↥(TwoChartCech.gluedLinesSections k a b lam n m).H0 ∧
        (Subsingleton (𝒲₀.sectionsOf x L).H1 ↔
          Subsingleton (TwoChartCech.gluedLinesSections k a b lam n m).H1) ∧
        (Nonempty (L ≅ SheafOfModules.unit X.ringCatSheaf) ↔ n = 0 ∧ m = 0 ∧ ∀ i j, lam i = lam j) ∧
        (Nonempty ((Scheme.Modules.pullback i₁).obj L ≅
            (Scheme.Modules.pullback i₁).obj (SheafOfModules.unit X.ringCatSheaf)) ↔ n = 0) ∧
        (Nonempty ((Scheme.Modules.pullback i₂).obj L ≅
            (Scheme.Modules.pullback i₂).obj (SheafOfModules.unit X.ringCatSheaf)) ↔ m = 0) ∧
        (∀ 𝒲' : M₁.C.TwoAffineOpenCover,
          (Module.finrank k ↥(𝒲'.sectionsOf M₁.toBase ((Scheme.Modules.pullback i₁).obj L)).H0 : ℤ) -
            Module.finrank k (𝒲'.sectionsOf M₁.toBase ((Scheme.Modules.pullback i₁).obj L)).H1 = n + 1) ∧
        (∀ 𝒲' : M₂.C.TwoAffineOpenCover,
          (Module.finrank k ↥(𝒲'.sectionsOf M₂.toBase ((Scheme.Modules.pullback i₂).obj L)).H0 : ℤ) -
            Module.finrank k (𝒲'.sectionsOf M₂.toBase ((Scheme.Modules.pullback i₂).obj L)).H1 = m + 1) := by sorry
