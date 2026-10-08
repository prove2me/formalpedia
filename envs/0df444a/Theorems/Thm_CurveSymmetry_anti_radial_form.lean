-- Prove2me | Theorems.Thm_CurveSymmetry_anti_radial_form
-- name    : CurveSymmetry.anti_radial_form
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:40:55.839618+00:00
-- url     : https://prove2.me/theorems/91d949c0-fd31-4811-9ce9-6537db4c6927
-- title:
--   Below degree $2m$, a polynomial with $P(\zeta X,\zeta^{-1}Y)=-P(X,Y)$ has the form $X^mA(XY)+Y^mB(XY)$
-- statement:
--   Let $m\ge 1$ be an integer and let $\zeta\in\mathbb C$ be a primitive $2m$-th root of unity. Let $P(X,Y)=\sum_{a,b\ge 0}p_{ab}X^aY^b\in\mathbb C[X,Y]$ be a polynomial of total degree $d<2m$ that changes sign under the substitution $(X,Y)\mapsto(\zeta X,\zeta^{-1}Y)$, that is, $P(\zeta X,\zeta^{-1}Y)=-P(X,Y)$. Collect the coefficients of $P$ of weight $a-b=m$ and of weight $a-b=-m$ into two polynomials in one variable $s$:
--   $A(s)=\sum_{k\ge 0}p_{k+m,\,k}\,s^k$ and $B(s)=\sum_{k\ge 0}p_{k,\,k+m}\,s^k$.
--
--   Then
--
--   $$
--   P(X,Y)=X^m\,A(XY)+Y^m\,B(XY),
--   $$
--
--   and both degrees are bounded: $\deg A\le\lfloor (d-m)/2\rfloor$ and $\deg B\le\lfloor (d-m)/2\rfloor$.
--
--   This is the algebraic core of equation (5) of the note. In the coordinates $X=z$, $Y=\bar z$ the substitution is the rotation $z\mapsto\zeta z$; in the proof of Theorem 1, a rotation of order $2m$ larger than the degree satisfies equation (4) with sign $-1$, and the statement shows that only the weights $a-b=\pm m$ can then occur. The refinement for irreducible polynomials with conjugate-symmetric coefficients, giving $P=X^mA(XY)+Y^m\overline{A}(XY)$ with $A$ nonconstant, is derived from it.
--
--   **Formalization Note**: degrees are natural numbers, with $\deg 0=0$, and $\lfloor (d-m)/2\rfloor$ is computed in $\mathbb N$, where $d-m$ is truncated at $0$.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for proof of Theorem 1, equation (5), p. 3, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/RadialAntiForm.lean (C. Perassi)

import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Data.Complex.Basic
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

theorem CurveSymmetry.anti_radial_form {m : ℕ} (hm : 0 < m) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (2 * m))
    {P : BPoly} (hdeg : P.totalDegree < 2 * m) (hanti : rotate ζ P = -P) :
    P = (X 0 : BPoly) ^ m * Polynomial.aeval ((X 0 : BPoly) * X 1) (weightPolynomial P m) +
        (X 1 : BPoly) ^ m *
          Polynomial.aeval ((X 0 : BPoly) * X 1) (oppositeWeightPolynomial P m) ∧
      (weightPolynomial P m).natDegree ≤ (P.totalDegree - m) / 2 ∧
      (oppositeWeightPolynomial P m).natDegree ≤ (P.totalDegree - m) / 2 := by sorry
