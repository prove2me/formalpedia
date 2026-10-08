-- Prove2me | Theorems.Thm_CurveSymmetry_quarticHolo_linearIndependent
-- name    : CurveSymmetry.quarticHolo_linearIndependent
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:46:21.569835+00:00
-- url     : https://prove2.me/theorems/1b950072-2b48-4fdf-beb1-b0def7d07572
-- title:
--   The differentials $dx/y^3$, $x\,dx/y^3$ and $dx/y^2$ of the quartic $x^4+y^4=2$ are linearly independent
-- statement:
--   Let $K_4=\mathbb C(x)[Y]/(Y^4-(2-x^4))$, with $y$ the class of $Y$, so that $x^4+y^4=2$. This is the function field of the quartic $X^4+Y^4=2$, written as the cover $y^4=2-x^4$ of the $x$-line; in the coordinates $X=z$, $Y=\bar z$ the real locus of that quartic is the curve $\operatorname{Re}(z^4)=1$ of Remark 5. Let $\Omega_{K_4/\mathbb C}$ be the module of Kähler differentials of $K_4$, with universal derivation $d$.
--
--   Then the three differentials $dx/y^3$, $x\,dx/y^3$ and $y\,dx/y^3=dx/y^2$ are linearly independent over $\mathbb C$ in $\Omega_{K_4/\mathbb C}$: for $c_0,c_1,c_2\in\mathbb C$,
--
--   $$c_0\,\frac{dx}{y^3}+c_1\,\frac{x\,dx}{y^3}+c_2\,\frac{dx}{y^2}=0\ \Longrightarrow\ c_0=c_1=c_2=0.$$
--
--   Since the three differentials are also holomorphic (regular at every place of $K_4$), the space of holomorphic differentials of the quartic has dimension at least three; this is the lower bound behind the genus three of $\operatorname{Re}(z^4)=1$ in Remark 5, against the genus two of the $m=2$ family.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for Remark 5, p. 4, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/FermatHolomorphic.lean (C. Perassi)

import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
import Definitions.Def_CurveSymmetry_06_QuadraticRing
import Definitions.Def_CurveSymmetry_08_Differentials
import Definitions.Def_CurveSymmetry_09_Genus
import Definitions.Def_CurveSymmetry_10_KummerField
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
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Tactic

open CurveSymmetry
set_option autoImplicit false
open Polynomial

theorem CurveSymmetry.quarticHolo_linearIndependent : LinearIndependent ℂ quarticHolo := by sorry
