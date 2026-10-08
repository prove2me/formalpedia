-- Prove2me | Theorems.Thm_CurveSymmetry_other_mixed_affine_points_image
-- name    : CurveSymmetry.other_mixed_affine_points_image
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:43:48.832429+00:00
-- url     : https://prove2.me/theorems/5073757a-7b62-4ae3-ba6c-6d521ba6b56a
-- title:
--   The chart change $(X,Y)\mapsto(1/Y,X)$ maps the affine curve with $Y\ne0$ onto the punctured mixed chart curve
-- statement:
--   Let $m\ge0$ be an integer and let $\alpha\in\mathbb C$ be arbitrary. Let $P_\alpha(X,Y)=X^m(\alpha+XY)+Y^m(\bar\alpha+XY)$ and $Q(v,x)=\bar\alpha v+x+\alpha v^{m+1}x^m+v^mx^{m+1}\in\mathbb C[v,x]$. For $v\ne0$ one has $Q(v,x)=v^{m+1}P_\alpha(x,1/v)$, so $Q$ is the equation of the curve $P_\alpha=0$ in the chart $v=1/Y$, $x=X$ around the boundary point $(0,\infty)$ of $\mathbb P^1\times\mathbb P^1$.
--
--   Then the map $(X,Y)\mapsto(1/Y,X)$ sends the points of the affine curve with $Y\ne0$ exactly onto the points of the chart curve with $v\ne0$:
--
--   $$
--   \bigl\{(1/Y,\,X):\ (X,Y)\in\mathbb C^2,\ P_\alpha(X,Y)=0,\ Y\ne0\bigr\}=\bigl\{(v,x)\in\mathbb C^2:\ Q(v,x)=0,\ v\ne0\bigr\}.
--   $$
--
--   This is the explicit correspondence, in both directions, between the affine curve $P_\alpha=0$ off the axis $Y=0$ and the second mixed chart curve off its axis $v=0$. The formalization uses it when the four standard charts are glued, to show that the zero set of the bihomogeneous equation lies in the closure of the curve (6) in $\mathbb P^1\times\mathbb P^1$.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for Section 3, closure of equation (6), p. 3, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/OtherMixedCornerClosure.lean (C. Perassi)

import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Spectrum.Prime.Jacobson
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic

open CurveSymmetry
set_option autoImplicit false
open MvPolynomial

theorem CurveSymmetry.other_mixed_affine_points_image (m : ℕ) (α : ℂ) :
    (fun z : Fin 2 → ℂ => ![(z 1)⁻¹, z 0]) ''
      {z | eval z (familyPolynomial m α) = 0 ∧ z 1 ≠ 0} =
      {w : Fin 2 → ℂ | eval w (familyMixedPolynomial m (star α) α) = 0 ∧
        w 0 ≠ 0} := by sorry
