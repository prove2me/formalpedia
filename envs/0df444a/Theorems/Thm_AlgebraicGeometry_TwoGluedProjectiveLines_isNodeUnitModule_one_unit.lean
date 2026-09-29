-- Prove2me | Theorems.Thm_AlgebraicGeometry_TwoGluedProjectiveLines_isNodeUnitModule_one_unit
-- name    : AlgebraicGeometry.TwoGluedProjectiveLines.isNodeUnitModule_one_unit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/851ed9fc-3828-5778-b620-f39c965bda94
-- title:
--   Structure sheaf of two glued lines is a node-unit module
-- statement:
--   Let $\kappa$ be an algebraically closed field, let $x\colon X\to\operatorname{Spec}\kappa$ be a morphism with $X$ reduced, and let $M_1,M_2$ be curve models of $\operatorname{RatFunc}\kappa$ over $\kappa$, i.e. integral schemes $M_j.C$ proper and smooth of relative dimension $1$ over $\kappa$, each equipped with a ring isomorphism of $\operatorname{RatFunc}\kappa$ with the function field compatible with $\kappa$, a bijection `placeEquiv` from the closed points to the places of $\operatorname{RatFunc}\kappa$ over $\kappa$ matching stalks with valuation subrings, and with every finite set of points contained in an affine open. Let $i_1\colon M_1.C\to X$ and $i_2\colon M_2.C\to X$ be closed immersions with $i_j$ followed by $x$ equal to the structure morphism $M_j.\mathrm{toBase}$, whose images cover $X$ as a set. Let $s\in\mathbb N$ and $a,b\colon \mathrm{Fin}\,s\to\kappa^\times$ with $a$ injective, and assume: for each $i$, the closed point of $M_1.C$ corresponding to the place of $X-a_i$ and the closed point of $M_2.C$ corresponding to the place of $X-b_i$ have the same image in $X$; conversely every pair of points with equal images is such a pair; and the scheme-theoretic pullback of $i_1$ and $i_2$ is reduced. Then for every $h\colon T\to\operatorname{Spec}\kappa$ the structure sheaf of $\operatorname{pullback} x\,h$, viewed as a module over itself, satisfies `IsNodeUnitModule` with gluing units all equal to $1$: there are morphisms $j_1,j_2$ from it to the pushforwards along $\mathrm{curveChange}\,i_1$, respectively $\mathrm{curveChange}\,i_2$, of the structure sheaves of $M_1.C\times_\kappa T$ and $M_2.C\times_\kappa T$ such that, over every open $W$ of $X\times_\kappa T$, the map $m\mapsto (j_1(m),j_2(m))$ on sections is injective with image exactly the set of pairs $(f,g)$ whose restrictions along the two node sections agree on the $i$-th node locus in $W$ for every $i$ (the unit factor being $1$).
--
--   This is the base-changed form of the exact sequence $0\to\mathcal O_X\to i_{1*}\mathcal O_{C_1}\oplus i_{2*}\mathcal O_{C_2}\to\bigoplus_{\text{nodes}}\kappa\to0$ for a reduced scheme that is the transversal union of two projective lines along $s$ nodes, recorded in the shape used for rigidified line bundles. It provides the base point of the node-unit description of line bundles and is used by [`AlgebraicGeometry.TwoGluedProjectiveLines.exists_isInvertible_isNodeUnitModule`](thm.html#AlgebraicGeometry.TwoGluedProjectiveLines.exists_isInvertible_isNodeUnitModule), [`AlgebraicGeometry.TwoGluedProjectiveLines.exists_isNodeUnitModule_pullback_of_pullback_iso_unit`](thm.html#AlgebraicGeometry.TwoGluedProjectiveLines.exists_isNodeUnitModule_pullback_of_pullback_iso_unit) and [`AlgebraicGeometry.TwoGluedProjectiveLines.isAlgEquivZero_of_pullback_iso_unit`](thm.html#AlgebraicGeometry.TwoGluedProjectiveLines.isAlgEquivZero_of_pullback_iso_unit).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_TwoGluedProjectiveLines_isNodeUnitModule_one_unit.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_TwoGluedProjectiveLinesNodeUnitModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve
  NeronModelInfra AlgebraicGeometry.TwoGluedProjectiveLines

theorem AlgebraicGeometry.TwoGluedProjectiveLines.isNodeUnitModule_one_unit
    (κ : Type u) [Field κ] [IsAlgClosed κ]
    {X : Scheme.{u}} (x : X ⟶ Spec (.of κ)) [IsReduced X]
    (M₁ M₂ : CurveModel κ (RatFunc κ)) (i₁ : M₁.C ⟶ X) (i₂ : M₂.C ⟶ X)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (hi₁ : i₁ ≫ x = M₁.toBase) (hi₂ : i₂ ≫ x = M₂.toBase)
    (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    {s : ℕ} (a b : Fin s → κˣ) (ha : Function.Injective a)
    (hnode : ∀ i, i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint κ (a i : κ))).1
                = i₂.base (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint κ (b i : κ))).1)
    (hinter : ∀ p q, i₁.base p = i₂.base q →
      ∃ i, p = (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint κ (a i))).1 ∧
        q = (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint κ (b i))).1)
    (htrans : IsReduced (pullback i₁ i₂))
    {T : Scheme.{u}} (h : T ⟶ Spec (.of κ)) :
    IsNodeUnitModule x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h 1 (SheafOfModules.unit (pullback x h).ringCatSheaf) := by sorry
