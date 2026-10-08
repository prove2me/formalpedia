-- Prove2me | Theorems.Thm_CurveSymmetry_quartic_not_similar_family
-- name    : CurveSymmetry.quartic_not_similar_family
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:46:06.89779+00:00
-- url     : https://prove2.me/theorems/50756aaa-0d59-4d4a-bf2a-b309ae22be78
-- title:
--   No orientation-preserving similarity maps the curve $\operatorname{Re}(z^4)=1$ onto a curve $C_{2,\alpha}$
-- statement:
--   Let $\alpha\in\mathbb C$ with $\alpha\ne\bar\alpha$, and let $C_{2,\alpha}=\{z\in\mathbb C:\ \operatorname{Re}\bigl(z^2(|z|^2+\alpha)\bigr)=0\}$, the set of equation (1) of the note with $m=2$; here only $\alpha\ne\bar\alpha$ is assumed, not $|\alpha|=1$. Both $C_{2,\alpha}$ and the quartic curve $\{z\in\mathbb C:\ \operatorname{Re}(z^4)=1\}$ are subsets of the plane $\mathbb C=\mathbb R^2$.
--
--   Then, for all $a,b\in\mathbb C$ with $a\ne0$, the orientation-preserving similarity $z\mapsto az+b$ does not map the quartic curve onto $C_{2,\alpha}$:
--
--   $$\{\,az+b:\ z\in\mathbb C,\ \operatorname{Re}(z^4)=1\,\}\ne C_{2,\alpha}.$$
--
--   This is the orientation-preserving half of the statement in Remark 5 that the degree-four curve $\operatorname{Re}(z^4)=1$, which attains the rotation bound of Theorem 1, is not in the $m=2$ family; the reason given there is that the genera are three and two.
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

theorem CurveSymmetry.quartic_not_similar_family {α : ℂ} (hα : α ≠ star α) {a b : ℂ} (ha : a ≠ 0) :
    (fun z : ℂ => a * z + b) '' {z : ℂ | (z ^ 4).re = 1} ≠ extremalCurve 2 α := by sorry
