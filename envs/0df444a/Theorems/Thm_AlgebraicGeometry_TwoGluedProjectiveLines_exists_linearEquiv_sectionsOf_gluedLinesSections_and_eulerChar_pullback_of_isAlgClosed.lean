-- Prove2me | Theorems.Thm_AlgebraicGeometry_TwoGluedProjectiveLines_exists_linearEquiv_sectionsOf_gluedLinesSections_and_eulerChar_pullback_of_isAlgClosed
-- name    : AlgebraicGeometry.TwoGluedProjectiveLines.exists_linearEquiv_sectionsOf_gluedLinesSections_and_eulerChar_pullback_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/4d90ea4e-f119-57e2-8b42-4c2b4ce7afd2
-- title:
--   Line bundles on two glued projective lines: Čech model
-- statement:
--   Let $k$ be an algebraically closed field, $X$ a reduced scheme with a morphism $x : X \to \operatorname{Spec} k$, and let $M_1, M_2$ be curve models of $\mathrm{RatFunc}\,k$ over $k$: integral schemes $M_j.C$, proper and smooth of relative dimension $1$ over $\operatorname{Spec} k$, together with an identification of $\mathrm{RatFunc}\,k$ with the function field over $k$, a bijection `placeEquiv` between closed points and places of $\mathrm{RatFunc}\,k$ over $k$ matching stalks with valuation rings, and the property that every finite set of points lies in an affine open. Let $i_1 : M_1.C \to X$, $i_2 : M_2.C \to X$ be closed immersions over $\operatorname{Spec} k$ (i.e. $i_j$ followed by $x$ is $M_j.\mathrm{toBase}$) whose images cover $X$. Let $a, b : \mathrm{Fin}\,s \to k^\times$ with $a$ injective, assume that for each $i$ the point of $M_1.C$ attached to the place $T = a_i$ and the point of $M_2.C$ attached to the place $T = b_i$ have the same image in $X$, that every coincidence $i_1(p) = i_2(q)$ is of this form, and that the scheme-theoretic intersection $\mathrm{pullback}\,i_1\,i_2$ is reduced. Let $\mathcal W_0$ be a two-affine open cover of $X$ (affine opens $U_0, U_1$ with $U_0 \sqcup U_1 = \top$ and $U_0 \sqcap U_1$ affine) whose traces on each $M_j.C$ are the complement of the point at infinity for $U_0$ and the complement of the point $T = 0$ for $U_1$. Finally let $L$ be a module on $X$ that is invertible in the sense that every point of $X$ has an open neighbourhood $U$ with the pullback of $L$ to $U$ isomorphic to the unit module. Then there exist $n, m \in \mathbb Z$ and $\lambda : \mathrm{Fin}\,s \to k^\times$ with the following properties. First, there are $k$-linear isomorphisms of $\Gamma(L, U_0)$, $\Gamma(L, U_1)$, $\Gamma(L, U_0 \sqcap U_1)$ with the three modules $M_0, M_1, M_{01}$ of [`TwoChartCech.gluedLinesSections k a b lam n m`](def/TwoChartCech_GluedLines.html#L126) commuting with both restriction maps $r_0, r_1$. Second, $L$ is isomorphic to the unit module on $X$ if and only if $n = 0$, $m = 0$ and $\lambda$ is constant. Third, the pullback of $L$ along $i_1$ is isomorphic to the pullback of the unit module if and only if $n = 0$, and likewise along $i_2$ if and only if $m = 0$. Fourth, for every two-affine open cover $\mathcal W'$ of $M_1.C$ the difference $\dim_k H^0 - \dim_k H^1$ of the associated two-chart Čech sections of the pullback of $L$ along $i_1$ equals $n+1$, where $H^0$ is the kernel and $H^1$ the cokernel of the Čech differential; and correspondingly the value $m+1$ for every two-affine open cover of $M_2.C$ and the pullback along $i_2$.
--
--   This is the line-bundle classification on a curve obtained by gluing two copies of the projective line transversally at $s$ labelled nodes: the Picard group is described by a bidegree $(n,m)$ together with gluing scalars $\lambda$ at the nodes, and the Čech section modules on a two-chart cover are identified with those of the explicit glued-lines model, with genus-zero Riemann–Roch pinning the Euler characteristics on the two components. It feeds the relative Picard and Néron-model infrastructure for such degenerate fibres, and the subsequent statements computing $H^0$ and $H^1$ dimensions for these section modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_TwoGluedProjectiveLines_exists_linearEquiv_sectionsOf_gluedLinesSections_and_eulerChar_pullback_of_isAlgClosed.lean

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

theorem AlgebraicGeometry.TwoGluedProjectiveLines.exists_linearEquiv_sectionsOf_gluedLinesSections_and_eulerChar_pullback_of_isAlgClosed
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
      (∃ (e₀ : (𝒲₀.sectionsOf x L).M0 ≃ₗ[k] (TwoChartCech.gluedLinesSections k a b lam n m).M0)
          (e₁ : (𝒲₀.sectionsOf x L).M1 ≃ₗ[k] (TwoChartCech.gluedLinesSections k a b lam n m).M1)
          (e₀₁ : (𝒲₀.sectionsOf x L).M01 ≃ₗ[k] (TwoChartCech.gluedLinesSections k a b lam n m).M01),
          (∀ t, e₀₁ ((𝒲₀.sectionsOf x L).r0 t) = (TwoChartCech.gluedLinesSections k a b lam n m).r0 (e₀ t)) ∧
          (∀ t, e₀₁ ((𝒲₀.sectionsOf x L).r1 t) = (TwoChartCech.gluedLinesSections k a b lam n m).r1 (e₁ t))) ∧
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
