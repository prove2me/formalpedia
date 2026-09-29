-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_normModule_curveChange_dualNumber_iso_unit_of_finrank_eq_char_of_forall_isClosed_eq
-- name    : AlgebraicGeometry.RelPicard.nonempty_normModule_curveChange_dualNumber_iso_unit_of_finrank_eq_char_of_forall_isClosed_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/fdaa0dad-b668-5e5c-bee0-0aaa149f0b27
-- title:
--   Norm along a degree-p cover trivialises first-order deformations
-- statement:
--   Let $\kappa$ be an algebraically closed field of characteristic a prime $p$, and let $C$, $C'$ be integral schemes equipped with morphisms $c : C \to \operatorname{Spec}\kappa$ and $c' : C' \to \operatorname{Spec}\kappa$, with $c$ locally of finite type, together with a two-chart affine open cover $\mathcal{V}$ of $C$ (two affine opens whose union is $C$ and whose intersection is again affine). Assume that every closed subset of $C$ other than $C$ itself is finite, and let $f : C' \to C$ be a morphism over $\kappa$ (i.e. $f$ followed by $c$ equals $c'$) which is finite, flat and locally of finite presentation, of constant rank $f.\mathrm{finrank}\,y = p$ at every point, and injective on closed points (any two closed points of $C'$ with the same image under $f$ coincide). Let $L$ be a module on the fibre product of $c'$ with $\operatorname{Spec}\kappa[\varepsilon] \to \operatorname{Spec}\kappa$ which is invertible in the sense that every point has an open neighbourhood on which $L$ restricts to the unit module, and assume that the pullback of $L$ along the base change of the reduction $\kappa[\varepsilon] \to \kappa$ (the map $\mathrm{baseChangeSnd}$ attached to $\mathrm{dualNumberReductionOver}$) is isomorphic to the unit module on the fibre product of $c'$ with $\operatorname{Spec}\kappa \to \operatorname{Spec}\kappa$. Then the norm module of $L$ in degree $p$ along the induced morphism $\mathrm{curveChange}\,f$ of $\kappa[\varepsilon]$-base changes, namely $\det_p$ of the pushforward of $L$ tensored with the dual of $\det_p$ of the pushforward of the unit module, is isomorphic to the unit module on the fibre product of $c$ with $\operatorname{Spec}\kappa[\varepsilon] \to \operatorname{Spec}\kappa$.
--
--   This is the vanishing of the norm map on first-order deformations of the trivial line bundle along a finite flat cover of degree $p$ in characteristic $p$ which is injective on closed points, reflecting the vanishing of the trace form of such a cover. It is used in the study of the relative Picard functor, where it feeds the statement that the norm induces the trivial map on the dual-number points of the relative $\mathrm{Pic}^0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_nonempty_normModule_curveChange_dualNumber_iso_unit_of_finrank_eq_char_of_forall_isClosed_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_RigKerDualNumber

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry
open AlgebraicGeometry.RelPicard

universe u

theorem AlgebraicGeometry.RelPicard.nonempty_normModule_curveChange_dualNumber_iso_unit_of_finrank_eq_char_of_forall_isClosed_eq
    {κ : Type u} [Field κ] [IsAlgClosed κ] {p : ℕ} [Fact p.Prime] [CharP κ p]
    {C C' : Scheme.{u}} [IsIntegral C] [IsIntegral C']
    (c : C ⟶ Spec (CommRingCat.of κ)) (c' : C' ⟶ Spec (CommRingCat.of κ))
    [LocallyOfFiniteType c] (𝒱 : C.TwoAffineOpenCover)

    (hC : ∀ Z : Set C, IsClosed Z → Z ≠ Set.univ → Z.Finite)
    (f : C' ⟶ C) (hf : f ≫ c = c')
    [IsFinite f] [Flat f] [LocallyOfFinitePresentation f] (hrk : ∀ y, f.finrank y = p)
    (hinj : ∀ x₁ x₂ : C', IsClosed ({x₁} : Set C') → IsClosed ({x₂} : Set C') → f.base x₁ = f.base x₂ → x₁ = x₂)

    (L : (pullback c' (Scheme.TwoAffineOpenCover.specMap κ (DualNumber κ))).Modules)
    (hL : Scheme.Modules.IsInvertible L)
    (h0 : Nonempty ((Scheme.Modules.pullback (RelPicard.baseChangeSnd c' (dualNumberReductionOver κ κ))).obj L ≅
      SheafOfModules.unit.{u} (pullback c' (Scheme.TwoAffineOpenCover.specMap κ κ)).ringCatSheaf)) :
    Nonempty (Scheme.Modules.normModule (curveChange f hf (Scheme.TwoAffineOpenCover.specMap κ (DualNumber κ))) p L ≅
      SheafOfModules.unit.{u} (pullback c (Scheme.TwoAffineOpenCover.specMap κ (DualNumber κ))).ringCatSheaf) := by sorry
