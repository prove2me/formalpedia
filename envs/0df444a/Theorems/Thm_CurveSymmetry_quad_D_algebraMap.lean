-- Prove2me | Theorems.Thm_CurveSymmetry_quad_D_algebraMap
-- name    : CurveSymmetry.quad_D_algebraMap
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:44:18.736281+00:00
-- url     : https://prove2.me/theorems/dd14b9f2-59b8-4e1d-8ca6-9125e3088d70
-- title:
--   Chain rule in $\mathbb C(t)[W]/(W^2-h)$: $d\big(p(t)\big)=p'(t)\,dt$ for every polynomial $p$
-- statement:
--   Let $h\in\mathbb C[t]$ be such that $W^2-h(t)$ is irreducible in $\mathbb C(t)[W]$, let $L_h=\mathbb C(t)[W]/(W^2-h(t))$, and let $d\colon L_h\to\Omega_{L_h/\mathbb C}$ be the universal derivation into the Kähler differentials of $L_h$ over $\mathbb C$. Then for every polynomial $p\in\mathbb C[t]$, viewed as an element of $L_h$,
--
--   $$
--   d\big(p(t)\big)=p'(t)\,dt,
--   $$
--
--   where $p'$ is the derivative of $p$.
--
--   This chain rule along $\mathbb C[t]\to L_h$ is used to differentiate the relation $w^2=h(t)$ and other polynomial expressions in $t$ when the differentials of the double cover (7) are computed, for the genus in Lemma 4 and for Remark 5.
--
--   **Formalization Note**: the irreducibility of $W^2-h(t)$ is a `Fact` instance.
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

theorem CurveSymmetry.quad_D_algebraMap (p : ℂ[X]) :
    KaehlerDifferential.D ℂ (QuadField h) (algebraMap ℂ[X] (QuadField h) p) =
      algebraMap ℂ[X] (QuadField h) p.derivative •
        KaehlerDifferential.D ℂ (QuadField h) (quadT h) := by sorry
