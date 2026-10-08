-- Prove2me | Theorems.Thm_CurveSymmetry_fourTermForm_proportional_iff
-- name    : CurveSymmetry.fourTermForm_proportional_iff
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:41:32.411951+00:00
-- url     : https://prove2.me/theorems/067c3626-8c12-4219-8161-00475109c5e7
-- title:
--   Two polynomials $aX^m+bY^m+XY(cX^m+dY^m)$ are proportional exactly when their coefficient vectors are
-- statement:
--   Let $m\ge1$ be an integer. For $a,b,c,d\in\mathbb C$ write $F_{a,b,c,d}(X,Y)=aX^m+bY^m+XY\,(cX^m+dY^m)\in\mathbb C[X,Y]$.
--
--   Then for all $a,b,c,d,A,B,C',D,k\in\mathbb C$,
--   $$F_{a,b,c,d}=k\,F_{A,B,C',D}\iff a=kA,\quad b=kB,\quad c=kC',\quad d=kD.$$
--
--   In the proof of Theorem 2, $P_\alpha=F_{\alpha,\bar\alpha,1,1}$, and the pullbacks of $P_\beta$ under $z\mapsto cz$ and, after clearing denominators, under $z\mapsto c/z$ are again of this form; this criterion turns their proportionality into the comparison of coefficients that yields the ratios (8). Through Theorem 2 it also serves Theorem 1 and Remark 5.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for proof of Theorem 2, equation (8), p. 4, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/FamilyTransport.lean (C. Perassi)

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
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic

open CurveSymmetry
set_option autoImplicit false
open MvPolynomial

theorem CurveSymmetry.fourTermForm_proportional_iff {m : ℕ} (hm : 0 < m) (a b c d A B C' D k : ℂ) :
    fourTermForm m a b c d = C k * fourTermForm m A B C' D ↔
      a = k * A ∧ b = k * B ∧ c = k * C' ∧ d = k * D := by sorry
