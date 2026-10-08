-- Prove2me | Theorems.Thm_CurveSymmetry_realLocus_fermat_four
-- name    : CurveSymmetry.realLocus_fermat_four
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:46:12.830798+00:00
-- url     : https://prove2.me/theorems/b36c753d-57e3-468c-9943-972668f1a32e
-- title:
--   In the coordinates $X=z$, $Y=\bar z$, the real locus of $X^4+Y^4-2$ is the curve $\operatorname{Re}(z^4)=1$
-- statement:
--   For a polynomial $R\in\mathbb C[X,Y]$, let $Z(R)=\{z\in\mathbb C:\ R(z,\bar z)=0\}$ be its real locus in the complex coordinates $X=z$, $Y=\bar z$.
--
--   For the Fermat quartic $X^4+Y^4-2$,
--
--   $$Z(X^4+Y^4-2)=\{z\in\mathbb C:\ z^4+\bar z^{\,4}=2\}=\{z\in\mathbb C:\ \operatorname{Re}(z^4)=1\}.$$
--
--   This identifies the degree-four curve $\operatorname{Re}(z^4)=1$ of Remark 5 with the real locus of the quartic $X^4+Y^4=2$, whose function field is where its holomorphic differentials, and hence its genus three, are computed; it is also used for the count of the rotations of that curve in Remark 5.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for Remark 5, p. 4, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/QuarticComparison.lean (C. Perassi)

import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
import Definitions.Def_CurveSymmetry_06_QuadraticRing
import Definitions.Def_CurveSymmetry_07_Places
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
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Spectrum.Maximal.Localization
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Tactic

open CurveSymmetry
set_option autoImplicit false
open Polynomial

theorem CurveSymmetry.realLocus_fermat_four : realLocus (fermatPolynomial 4) = {z : ℂ | (z ^ 4).re = 1} := by sorry
