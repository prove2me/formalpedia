-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_eq_of_isAlgEquivZero_of_nonempty_tensor_lineBundle_iso_lineBundle
-- name    : AlgebraicGeometry.RelEffCartierDiv.eq_of_isAlgEquivZero_of_nonempty_tensor_lineBundle_iso_lineBundle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/78198c7a-a27d-563c-9798-01513ccff457
-- title:
--   Algebraic equivalence to zero forces equal divisor degrees
-- statement:
--   Let $f : \mathcal{C} \to S$ be a separated morphism of schemes that is smooth of relative dimension one and geometrically integral, let $k$ be an algebraically closed field and $x : \operatorname{Spec} k \to S$ a $k$-point of $S$ whose base change $\mathrm{pr}_2 : \mathcal{C} \times_S \operatorname{Spec} k \to \operatorname{Spec} k$ is proper. Let $\mathcal{V}$ be a two-chart affine open cover of the fibre $\mathcal{C}\times_S\operatorname{Spec} k$, i.e. two affine opens $U_0, U_1$ with affine intersection and $U_0 \sqcup U_1 = \top$. Let $E_1, E_2$ be relative effective Cartier divisors over $x$ of degrees $r_1, r_2 \in \mathbb{N}$: each consists of an ideal sheaf datum on the fibre whose closed subscheme, mapped to $\operatorname{Spec} k$, is finite, flat and locally of finite presentation with fibre rank identically $r_1$, resp. $r_2$; write $E_i.\mathrm{lineBundle}$ for the dual of the module attached to that ideal. Let $\mathcal{L}$ be a module on the fibre that is invertible (locally isomorphic to the unit module) and satisfies `IsAlgEquivZero` for $\mathrm{pr}_2$: there are a geometrically integral $h : T' \to \operatorname{Spec} k$ locally of finite type, an invertible module $M$ on the fibre product of $\mathrm{pr}_2$ with $h$, and two sections $t_0, t_1$ of $h$ over $\operatorname{Spec} k$ such that the base-change pullback of $M$ along $t_0$ is isomorphic to the unit module and along $t_1$ to the pullback of $\mathcal{L}$. If $\mathcal{L} \otimes E_2.\mathrm{lineBundle} \cong E_1.\mathrm{lineBundle}$, then $r_1 = r_2$.
--
--   This is the statement that the degree of an effective divisor on a smooth proper integral curve over an algebraically closed field is an invariant of the algebraic equivalence class of its associated line bundle; equivalently, a line bundle algebraically equivalent to zero has degree zero. It is the degree component of the analysis of the relative Picard functor, and is cited in the form in which the fibre is obtained by pulling back along a morphism to a product.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelEffCartierDiv_eq_of_isAlgEquivZero_of_nonempty_tensor_lineBundle_iso_lineBundle.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.RelPicard

theorem AlgebraicGeometry.RelEffCartierDiv.eq_of_isAlgEquivZero_of_nonempty_tensor_lineBundle_iso_lineBundle
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsSeparated f] [SmoothOfRelativeDimension 1 f] [GeometricallyIntegral f]
    {k : Type u} [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ S) [IsProper (pullback.snd f x)]
    (𝒱 : (pullback f x).TwoAffineOpenCover)
    {r₁ r₂ : ℕ} (E₁ : RelEffCartierDiv f r₁ x) (E₂ : RelEffCartierDiv f r₂ x)
    (ℒ : (pullback f x).Modules) (hℒ : Scheme.Modules.IsInvertible ℒ)
    (h0 : IsAlgEquivZero (pullback.snd f x) ℒ)
    (e : Nonempty (ℒ ⊗ E₂.lineBundle ≅ E₁.lineBundle)) :
    r₁ = r₂ := by sorry
