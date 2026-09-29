-- Prove2me | Theorems.Thm_AlgebraicGeometry_TwoGluedProjectiveLines_isAlgEquivZero_of_pullback_iso_unit
-- name    : AlgebraicGeometry.TwoGluedProjectiveLines.isAlgEquivZero_of_pullback_iso_unit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/e4ddc956-5925-5dfe-aab8-243b838da93b
-- title:
--   Bundles trivial on both lines of a transversal gluing are algebraically equivalent to zero
-- statement:
--   Let $\kappa$ be an algebraically closed field and let $x\colon X \to \operatorname{Spec}\kappa$ be a morphism of schemes with $X$ reduced and $x$ separated. Let $M_1, M_2$ be two `CurveModel`s of $\mathrm{RatFunc}\,\kappa$ over $\kappa$, i.e. each consists of an integral scheme $M_j.C$ proper and smooth of relative dimension $1$ over $\kappa$, a ring isomorphism of $\kappa(t)$ with the function field of $M_j.C$ compatible with the structure morphism, and a bijection `placeEquiv` from the closed points of $M_j.C$ onto the places of $\kappa(t)/\kappa$ (places being valuation subrings containing $\kappa$, proper and principal) matching stalks with valuation subrings, together with the property that every finite set of points lies in one affine open. Let $i_1\colon M_1.C \to X$ and $i_2\colon M_2.C \to X$ be closed immersions with $i_1 \circ x = M_1.\mathrm{toBase}$, $i_2 \circ x = M_2.\mathrm{toBase}$, whose images cover $X$ topologically. Let $s \in \mathbb{N}$ and $a, b\colon \mathrm{Fin}\,s \to \kappa^\times$ with $a$ injective; writing $\alpha_i$, $\beta_i$ for the closed points of $M_1.C$, $M_2.C$ corresponding under `placeEquiv` to the finite places attached to $X - a_i$, $X - b_i$, assume $i_1(\alpha_i) = i_2(\beta_i)$ for all $i$, and conversely that any $p, q$ with $i_1(p) = i_2(q)$ is of the form $(\alpha_i, \beta_i)$; assume also that the scheme $M_1.C \times_X M_2.C$ is reduced. Finally let $L$ be a module on $X$ that is invertible (every point has an open neighbourhood over which $L$ pulls back to the unit sheaf) and such that both $i_1^* L$ and $i_2^* L$ admit isomorphisms with the corresponding pullbacks of the unit sheaf of $X$. The conclusion, `IsAlgEquivZero x L`, asserts the existence of a scheme $T'$ with a morphism $h\colon T' \to \operatorname{Spec}\kappa$ that is locally of finite type and geometrically integral, an invertible module $M$ on $X \times_{\operatorname{Spec}\kappa} T'$, and two sections $t_0, t_1$ of $h$, such that the pullback of $M$ along the base change of $t_0$ is isomorphic to the unit sheaf on $X \times_{\operatorname{Spec}\kappa} \operatorname{Spec}\kappa$ while the pullback of $M$ along the base change of $t_1$ is isomorphic to the pullback of $L$ along the first projection.
--
--   This is the connectedness of the degree-$(0,0)$ part of the Picard group of a curve obtained by gluing two projective lines transversally at $s$ points: such a class, being trivial on each component, is captured by gluing units at the nodes and hence moves in an algebraic family parametrised by a torus. It serves as the special-fibre input for identifying classes algebraically equivalent to zero on relative Picard functors, and is used in the treatment of fibres of the relative Picard functor for two-line degenerations and for the Deligne–Rapoport model of a modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_TwoGluedProjectiveLines_isAlgEquivZero_of_pullback_iso_unit.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve

theorem AlgebraicGeometry.TwoGluedProjectiveLines.isAlgEquivZero_of_pullback_iso_unit
    (κ : Type u) [Field κ] [IsAlgClosed κ] [DecidableEq (RatFunc κ)]
    {X : Scheme.{u}} (x : X ⟶ Spec (.of κ)) [IsReduced X] [IsSeparated x]
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
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (h₁ : Nonempty ((Scheme.Modules.pullback i₁).obj L ≅
      (Scheme.Modules.pullback i₁).obj (SheafOfModules.unit X.ringCatSheaf)))
    (h₂ : Nonempty ((Scheme.Modules.pullback i₂).obj L ≅
      (Scheme.Modules.pullback i₂).obj (SheafOfModules.unit X.ringCatSheaf))) :
    IsAlgEquivZero x L := by sorry
