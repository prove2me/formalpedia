-- Prove2me | Theorems.Thm_CurveSymmetry_quad_kaehler_span_eq_top
-- name    : CurveSymmetry.quad_kaehler_span_eq_top
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:44:41.160191+00:00
-- url     : https://prove2.me/theorems/875eab81-c5ad-4ac0-a590-a21def44a179
-- title:
--   The Kähler differentials of $\mathbb C(t)[W]/(W^2-h)$ over $\mathbb C$ are spanned by $dt$
-- statement:
--   Let $h\in\mathbb C[t]$ be such that $W^2-h(t)$ is irreducible in $\mathbb C(t)[W]$, and let $L_h=\mathbb C(t)[W]/(W^2-h(t))$, a quadratic field extension of $\mathbb C(t)$. Let $\Omega_{L_h/\mathbb C}$ be the $L_h$-module of Kähler differentials of $L_h$ over $\mathbb C$, with universal derivation $d$. Then
--
--   $$
--   \Omega_{L_h/\mathbb C}=L_h\,dt,
--   $$
--
--   that is, the single differential $dt$ spans $\Omega_{L_h/\mathbb C}$ over $L_h$.
--
--   Every differential of the double cover is therefore a multiple of $dt$. In the formalization the genus in Lemma 4 is obtained from an explicit basis $t^i\,dt/w$, $0\le i<m$, of the holomorphic differentials of the double cover (7), and this statement is where that computation starts; it also serves Remark 5.
--
--   **Formalization Note**: the irreducibility of $W^2-h(t)$ is a `Fact` instance; $h$ is not assumed squarefree.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for Lemma 4, pp. 3-4, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/QuadraticDifferentials.lean (C. Perassi)

import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
import Definitions.Def_CurveSymmetry_06_QuadraticRing
import Definitions.Def_CurveSymmetry_08_Differentials
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic

open CurveSymmetry
set_option autoImplicit false
open Polynomial TensorProduct
variable (h : ℂ[X]) [Fact (Irreducible (quadRat h))]

theorem CurveSymmetry.quad_kaehler_span_eq_top :
    Submodule.span (QuadField h) {KaehlerDifferential.D ℂ (QuadField h) (quadT h)} = ⊤ := by sorry
