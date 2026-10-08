-- Prove2me | Theorems.Thm_CurveSymmetry_other_mixed_corner_mem_affine_closure
-- name    : CurveSymmetry.other_mixed_corner_mem_affine_closure
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:43:45.177355+00:00
-- url     : https://prove2.me/theorems/e9ce0213-ad8d-4193-b24d-f7f53a01f8a9
-- title:
--   The boundary point $(0,\infty)$ lies in the Zariski closure of $P_\alpha=0$ in the chart $(1/Y,X)$
-- statement:
--   Let $m\ge1$ be an integer and let $\alpha\in\mathbb C$ be arbitrary. Let $P_\alpha(X,Y)=X^m(\alpha+XY)+Y^m(\bar\alpha+XY)$ be the polynomial of equation (6). Near $Y=\infty$, use the chart of $\mathbb P^1\times\mathbb P^1$ with coordinates taken in the order $(v,X)$, where $v=1/Y$: a point $(X,Y)$ with $Y\ne0$ has chart coordinates $(1/Y,X)$, and the chart origin $(0,0)$ represents the boundary point $(X,Y)=(0,\infty)$. Let $\operatorname{Spec}\mathbb C[v,X]$ be the prime spectrum of the polynomial ring in the chart coordinates, with its Zariski topology, and for $w\in\mathbb C^2$ let $\mathfrak m_w$ be the maximal ideal of the polynomials vanishing at $w$.
--
--   Then the chart origin lies in the closure of the points of the affine curve $P_\alpha=0$ with $Y\ne0$, written in the chart coordinates:
--
--   $$\mathfrak m_{(0,0)}\in\overline{\bigl\{\mathfrak m_{(1/Y,\,X)}\ :\ (X,Y)\in\mathbb C^2,\ P_\alpha(X,Y)=0,\ Y\ne0\bigr\}}.$$
--
--   This is one of the chart computations behind $V_\alpha$, the closure of the curve (6) in $\mathbb P^1\times\mathbb P^1$, which the note introduces before Lemma 4 as a curve of bidegree $(m+1,m+1)$. It places the boundary point $(0,\infty)$ in the closure of the affine curve within this chart; gluing the charts into a global statement is a separate step.
--
--   **Formalization Note**: points of $\mathbb C^2$ are sent into the prime spectrum by $w\mapsto\mathfrak m_w$, the kernel of evaluation at $w$, and the closure is taken in Mathlib's Zariski topology on the prime spectrum.
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

theorem CurveSymmetry.other_mixed_corner_mem_affine_closure {m : ℕ} (hm : 0 < m) (α : ℂ) :
    affineSpectrumPoint ![0, 0] ∈
      closure ((fun z : Fin 2 → ℂ => affineSpectrumPoint ![(z 1)⁻¹, z 0]) ''
        {z | eval z (familyPolynomial m α) = 0 ∧ z 1 ≠ 0}) := by sorry
