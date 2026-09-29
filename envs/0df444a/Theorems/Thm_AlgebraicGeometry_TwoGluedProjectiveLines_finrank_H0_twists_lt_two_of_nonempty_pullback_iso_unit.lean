-- Prove2me | Theorems.Thm_AlgebraicGeometry_TwoGluedProjectiveLines_finrank_H0_twists_lt_two_of_nonempty_pullback_iso_unit
-- name    : AlgebraicGeometry.TwoGluedProjectiveLines.finrank_H0_twists_lt_two_of_nonempty_pullback_iso_unit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/afdfe498-1d6c-5db3-abd3-3b050c746d1c
-- title:
--   Trivial pullbacks of L force h⁰(M_±)<2
-- statement:
--   Let $k$ be an algebraically closed field and let $X$ be a reduced scheme with a morphism $x : X \to \operatorname{Spec} k$. Let $M_1, M_2$ be curve models of $\mathrm{RatFunc}\,k$ over $k$ — integral schemes, proper and smooth of relative dimension $1$ over $\operatorname{Spec} k$, together with an identification of the function field with $k(t)$ and a bijection between closed points and places — and let $i_1 : M_1.C \to X$, $i_2 : M_2.C \to X$ be closed immersions compatible with the structure morphisms ($i_j \cdot x$ equal to $M_j.\mathrm{toBase}$) whose images cover $X$. Fix $s$ and units $a, b : \mathrm{Fin}\,s \to k^\times$ with $a$ injective such that, for each $i$, the closed point of $M_1.C$ attached to the place $\mathrm{placeOfPoint}(a_i)$ and the closed point of $M_2.C$ attached to $\mathrm{placeOfPoint}(b_i)$ have the same image in $X$, and such that every coincidence $i_1(p) = i_2(q)$ arises in this way; assume moreover that $M_1.C \times_X M_2.C$ is reduced. Let $\mathcal{W}_0$ be a two-chart affine open cover of $X$ (two affine opens $U_0, U_1$ covering $X$ with affine intersection) whose preimage under $i_j$ is the complement of the point at infinity for $U_0$ and the complement of the point $0$ for $U_1$, on both curves. Let $g \in \mathbb{N}$ be such that the two-chart Čech complex of the unit sheaf of modules on $X$ relative to $\mathcal{W}_0$ has $\dim_k H^0 = 1$ and $\dim_k H^1 = g$, where $H^0$ is the kernel and $H^1$ the cokernel of the Čech differential. Let $L, M_+, M_-$ be invertible $\mathcal{O}_X$-modules (each locally isomorphic, after pullback along an open immersion, to the unit sheaf), and assume the Euler-characteristic bookkeeping: for every two-chart affine open cover $\mathcal{W}'$ of $M_1.C$, $\chi(i_1^*M_+) = 2\chi(i_1^*L) - 1 + g$ and $\chi(i_1^*M_-) = 3 - 2\chi(i_1^*L) + g$, and for every two-chart affine open cover of $M_2.C$, $\chi(i_2^*M_+) = 2\chi(i_2^*L) - 1$ and $\chi(i_2^*M_-) = 3 - 2\chi(i_2^*L)$, all Euler characteristics being $\dim_k H^0 - \dim_k H^1$ of the corresponding two-chart Čech complex. Finally assume that the pullbacks $i_1^*L$ and $i_2^*L$ are each isomorphic to the pullback of the unit sheaf of $X$. Then $\dim_k H^0(\mathcal{W}_0, M_+) < 2$ and $\dim_k H^0(\mathcal{W}_0, M_-) < 2$.
--
--   This is the forward half of a criterion, on a fibre which is a transversal union of two rational curves meeting in $s$ nodes, for an invertible sheaf to be algebraically equivalent to zero: triviality of $L$ on each of the two components is converted, through the prescribed Euler characteristics, into the numerical tests $h^0(M_\pm) < 2$. It is used in the identification of the locus of classes algebraically equivalent to zero on such fibres as an open condition in the relative Picard functor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_TwoGluedProjectiveLines_finrank_H0_twists_lt_two_of_nonempty_pullback_iso_unit.lean

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

theorem AlgebraicGeometry.TwoGluedProjectiveLines.finrank_H0_twists_lt_two_of_nonempty_pullback_iso_unit
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
    (h₁ : Nonempty ((Scheme.Modules.pullback i₁).obj L ≅ (Scheme.Modules.pullback i₁).obj (SheafOfModules.unit X.ringCatSheaf)))
    (h₂ : Nonempty ((Scheme.Modules.pullback i₂).obj L ≅ (Scheme.Modules.pullback i₂).obj (SheafOfModules.unit X.ringCatSheaf))) :
    Module.finrank k ↥(𝒲₀.sectionsOf x Mp).H0 < 2 ∧ Module.finrank k ↥(𝒲₀.sectionsOf x Mm).H0 < 2 := by sorry
