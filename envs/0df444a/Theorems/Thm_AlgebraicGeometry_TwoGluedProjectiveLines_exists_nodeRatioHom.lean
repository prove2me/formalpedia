-- Prove2me | Theorems.Thm_AlgebraicGeometry_TwoGluedProjectiveLines_exists_nodeRatioHom
-- name    : AlgebraicGeometry.TwoGluedProjectiveLines.exists_nodeRatioHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/1d66a954-5100-55a2-93c7-90f3da093cde
-- title:
--   Node-ratio invariant for two glued projective lines
-- statement:
--   Let $k$ be an algebraically closed field (with decidable equality on $\mathrm{RatFunc}\,k$ assumed), let $x : X \to \operatorname{Spec} k$ be a morphism of schemes with $X$ reduced and $x$ locally of finite type, and let $M_1, M_2$ be objects of `CurveModel k (RatFunc k)`: each consists of an integral scheme $C$ proper and smooth of relative dimension $1$ over $\operatorname{Spec} k$, a ring isomorphism $\mathrm{RatFunc}\,k \cong \mathcal{K}(C)$ over $k$, and a bijection `placeEquiv` from the closed points of $C$ to the places of $\mathrm{RatFunc}\,k$ over $k$ matching stalks with valuation subrings, every finite set of points lying in an affine open. Let $i_1 : M_1.C \to X$ and $i_2 : M_2.C \to X$ be closed immersions over $\operatorname{Spec} k$ (i.e. $i_j$ followed by $x$ equals $M_j.\mathrm{toBase}$) whose images cover $X$, with $\operatorname{pullback} i_1\, i_2$ reduced. Let $s \in \mathbb{N}$ and $a, b : \mathrm{Fin}\,s \to k^\times$ with $a$ injective, such that for each $i$ the closed points of $M_1.C$ and $M_2.C$ corresponding under `placeEquiv` to the places of $k(T)$ attached to $T - a_i$, respectively $T - b_i$, have the same image in $X$, and such that every coincidence $i_1(p) = i_2(q)$ of points arises in this way. Then there is a function $\delta$ from the sheaves of modules on $X$ to the quotient of $\mathrm{Fin}\,s \to k^\times$ by the range of the diagonal homomorphism $k^\times \to (\mathrm{Fin}\,s \to k^\times)$ such that: $\delta$ takes equal values on isomorphic modules; $\delta$ of the unit module $\mathcal{O}_X$ is $1$; for invertible $L, L'$ (locally, about each point, isomorphic to the unit module after restriction) whose pullbacks along $i_1$ and along $i_2$ are each isomorphic to the corresponding pullback of the unit module, $\delta(L \otimes L') = \delta(L)\,\delta(L')$; and for such an invertible $L$ with $\delta(L) = 1$, $L$ is isomorphic to the unit module.
--
--   This is the classical description of the identity component of the Picard group of a curve obtained by gluing two projective lines transversally at $s$ points: a line bundle trivial on each component is recorded by the tuple of ratios of trivialisations at the nodes, well defined modulo a single scalar, and this invariant detects triviality. It is used in the construction of the Deligne–Rapoport model package for modular curves, where it supplies an injective homomorphism out of the relevant group of components of a degenerate fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_TwoGluedProjectiveLines_exists_nodeRatioHom.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_TwoChartCech_GluedLines
import Definitions.Def_SheafOfModules_Monoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicCurve

universe u

theorem AlgebraicGeometry.TwoGluedProjectiveLines.exists_nodeRatioHom
    (k : Type u) [Field k] [IsAlgClosed k] [DecidableEq (RatFunc k)]
    {X : Scheme.{u}} (x : X ⟶ Spec (.of k)) [IsReduced X] [LocallyOfFiniteType x]
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
    :
    ∃ δ : X.Modules → (Fin s → kˣ) ⧸ (Pi.constMonoidHom (Fin s) kˣ).range,

      (∀ L L' : X.Modules, Nonempty (L ≅ L') → δ L = δ L') ∧

      δ (SheafOfModules.unit X.ringCatSheaf) = 1 ∧

      (∀ L L' : X.Modules, Scheme.Modules.IsInvertible L → Scheme.Modules.IsInvertible L' →
        Nonempty ((Scheme.Modules.pullback i₁).obj L ≅ (Scheme.Modules.pullback i₁).obj (SheafOfModules.unit X.ringCatSheaf)) →
        Nonempty ((Scheme.Modules.pullback i₂).obj L ≅ (Scheme.Modules.pullback i₂).obj (SheafOfModules.unit X.ringCatSheaf)) →
        Nonempty ((Scheme.Modules.pullback i₁).obj L' ≅ (Scheme.Modules.pullback i₁).obj (SheafOfModules.unit X.ringCatSheaf)) →
        Nonempty ((Scheme.Modules.pullback i₂).obj L' ≅ (Scheme.Modules.pullback i₂).obj (SheafOfModules.unit X.ringCatSheaf)) →
        δ (L ⊗ L') = δ L * δ L') ∧

      (∀ L : X.Modules, Scheme.Modules.IsInvertible L →
        Nonempty ((Scheme.Modules.pullback i₁).obj L ≅ (Scheme.Modules.pullback i₁).obj (SheafOfModules.unit X.ringCatSheaf)) →
        Nonempty ((Scheme.Modules.pullback i₂).obj L ≅ (Scheme.Modules.pullback i₂).obj (SheafOfModules.unit X.ringCatSheaf)) →
        δ L = 1 → Nonempty (L ≅ SheafOfModules.unit X.ringCatSheaf)) := by sorry
