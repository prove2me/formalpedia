-- Prove2me | Theorems.Thm_AlgebraicGeometry_TwoGluedProjectiveLines_nonempty_pullback_iso_unit_of_finrank_H0_twists_lt_two
-- name    : AlgebraicGeometry.TwoGluedProjectiveLines.nonempty_pullback_iso_unit_of_finrank_H0_twists_lt_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/3a52661c-242d-596c-aa06-859982c68691
-- title:
--   Triviality on both lines when h⁰ of both twists is <2
-- statement:
--   Let $k$ be an algebraically closed field, let $X$ be a reduced scheme with a morphism $x : X \to \operatorname{Spec} k$, and let $M_1, M_2$ be curve models of $k(t)$ over $k$ (proper smooth integral $k$-schemes of relative dimension $1$ whose closed points are in bijection, via `placeEquiv`, with the places of $k(t)/k$, with the further properties recorded in `CurveModel`). Let $i_1 : M_1.C \to X$ and $i_2 : M_2.C \to X$ be closed immersions over $k$ (so $i_j$ followed by $x$ is $M_j.\mathrm{toBase}$) whose images cover $X$. Let $a, b : \mathrm{Fin}\,s \to k^\times$ with $a$ injective be such that, for each $i$, $i_1$ and $i_2$ identify the closed points of $M_1.C$ and $M_2.C$ attached to the places $\mathrm{placeOfPoint}(a_i)$ and $\mathrm{placeOfPoint}(b_i)$, and such that every coincidence $i_1(p) = i_2(q)$ arises in this way; assume moreover $\mathrm{pullback}\,i_1\,i_2$ is reduced. Let $\mathcal W_0$ be a two-affine open cover of $X$ (two affine opens $U_0, U_1$ with $U_0 \sqcup U_1 = \top$ and $U_0 \sqcap U_1$ affine) whose traces on $M_1.C$ and $M_2.C$ are, for $U_0$, the complement of the point at infinity, and for $U_1$, the complement of the point $0$. Here $H^0$ and $H^1$ of a module $M$ on $X$ denote the kernel and the cokernel of the two-chart Čech differential $\Gamma(M,U_0) \times \Gamma(M,U_1) \to \Gamma(M, U_0 \sqcap U_1)$, as $k$-vector spaces. Assume $\dim_k H^0(\mathcal W_0, \mathcal O_X) = 1$ and $\dim_k H^1(\mathcal W_0, \mathcal O_X) = g$ for some natural number $g$, where $\mathcal O_X$ is the unit sheaf of modules. Let $L$, $M_+$, $M_-$ be $X$-modules that are invertible in the sense that each point of $X$ has an open neighbourhood on which the pullback is isomorphic to the unit, and assume that for every two-affine open cover of $M_1.C$ and of $M_2.C$ the Čech Euler characteristics satisfy $\chi(i_1^*M_+) = 2\chi(i_1^*L) - 1 + g$, $\chi(i_2^*M_+) = 2\chi(i_2^*L) - 1$, $\chi(i_1^*M_-) = 3 - 2\chi(i_1^*L) + g$ and $\chi(i_2^*M_-) = 3 - 2\chi(i_2^*L)$. If $\dim_k H^0(\mathcal W_0, M_+) < 2$ and $\dim_k H^0(\mathcal W_0, M_-) < 2$, then both $i_1^*L \cong i_1^*\mathcal O_X$ and $i_2^*L \cong i_2^*\mathcal O_X$ (the conclusion asserts that the two isomorphism types are nonempty).
--
--   This is the backward direction of a fibre criterion for triviality of a line bundle on a degenerate fibre consisting of two projective lines glued transversally at $s$ nodes: smallness of $h^0$ of the two twists $M_\pm$ of $L$ forces $L$ to have bidegree $(0,0)$, hence to be trivial on each line. It feeds the description of the locus in the relative Picard functor cut out by the vanishing of classes on two-line degenerations, used in [`AlgebraicGeometry.RelPicard.exists_isOpen_inter_preimage_eq_setOf_isAlgEquivZero_fibre_of_smoothLocus_of_twoLineDegenerations`](thm.html#AlgebraicGeometry.RelPicard.exists_isOpen_inter_preimage_eq_setOf_isAlgEquivZero_fibre_of_smoothLocus_of_twoLineDegenerations).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_TwoGluedProjectiveLines_nonempty_pullback_iso_unit_of_finrank_H0_twists_lt_two.lean

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

open TwoChartCech

theorem AlgebraicGeometry.TwoGluedProjectiveLines.nonempty_pullback_iso_unit_of_finrank_H0_twists_lt_two
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
    (g : ℕ)
    (hH0 : Module.finrank k ↥(𝒲₀.sectionsOf x (SheafOfModules.unit X.ringCatSheaf)).H0 = 1)
    (hH1 : Module.finrank k (𝒲₀.sectionsOf x (SheafOfModules.unit X.ringCatSheaf)).H1 = g)
    (L Mp Mm : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (hMp : Scheme.Modules.IsInvertible Mp) (hMm : Scheme.Modules.IsInvertible Mm)

    (hχp₁ : ∀ 𝒲' : M₁.C.TwoAffineOpenCover, (Module.finrank k ↥(𝒲'.sectionsOf M₁.toBase ((Scheme.Modules.pullback i₁).obj Mp)).H0 : ℤ) -
            Module.finrank k (𝒲'.sectionsOf M₁.toBase ((Scheme.Modules.pullback i₁).obj Mp)).H1 = 2 * ((Module.finrank k ↥(𝒲'.sectionsOf M₁.toBase ((Scheme.Modules.pullback i₁).obj L)).H0 : ℤ) -
            Module.finrank k (𝒲'.sectionsOf M₁.toBase ((Scheme.Modules.pullback i₁).obj L)).H1) - 1 + g)
    (hχp₂ : ∀ 𝒲' : M₂.C.TwoAffineOpenCover, (Module.finrank k ↥(𝒲'.sectionsOf M₂.toBase ((Scheme.Modules.pullback i₂).obj Mp)).H0 : ℤ) -
            Module.finrank k (𝒲'.sectionsOf M₂.toBase ((Scheme.Modules.pullback i₂).obj Mp)).H1 = 2 * ((Module.finrank k ↥(𝒲'.sectionsOf M₂.toBase ((Scheme.Modules.pullback i₂).obj L)).H0 : ℤ) -
            Module.finrank k (𝒲'.sectionsOf M₂.toBase ((Scheme.Modules.pullback i₂).obj L)).H1) - 1)
    (hχm₁ : ∀ 𝒲' : M₁.C.TwoAffineOpenCover, (Module.finrank k ↥(𝒲'.sectionsOf M₁.toBase ((Scheme.Modules.pullback i₁).obj Mm)).H0 : ℤ) -
            Module.finrank k (𝒲'.sectionsOf M₁.toBase ((Scheme.Modules.pullback i₁).obj Mm)).H1 = 3 - 2 * ((Module.finrank k ↥(𝒲'.sectionsOf M₁.toBase ((Scheme.Modules.pullback i₁).obj L)).H0 : ℤ) -
            Module.finrank k (𝒲'.sectionsOf M₁.toBase ((Scheme.Modules.pullback i₁).obj L)).H1) + g)
    (hχm₂ : ∀ 𝒲' : M₂.C.TwoAffineOpenCover, (Module.finrank k ↥(𝒲'.sectionsOf M₂.toBase ((Scheme.Modules.pullback i₂).obj Mm)).H0 : ℤ) -
            Module.finrank k (𝒲'.sectionsOf M₂.toBase ((Scheme.Modules.pullback i₂).obj Mm)).H1 = 3 - 2 * ((Module.finrank k ↥(𝒲'.sectionsOf M₂.toBase ((Scheme.Modules.pullback i₂).obj L)).H0 : ℤ) -
            Module.finrank k (𝒲'.sectionsOf M₂.toBase ((Scheme.Modules.pullback i₂).obj L)).H1))
    (hp : Module.finrank k ↥(𝒲₀.sectionsOf x Mp).H0 < 2) (hm : Module.finrank k ↥(𝒲₀.sectionsOf x Mm).H0 < 2) :
    Nonempty ((Scheme.Modules.pullback i₁).obj L ≅ (Scheme.Modules.pullback i₁).obj (SheafOfModules.unit X.ringCatSheaf)) ∧
    Nonempty ((Scheme.Modules.pullback i₂).obj L ≅ (Scheme.Modules.pullback i₂).obj (SheafOfModules.unit X.ringCatSheaf)) := by sorry
