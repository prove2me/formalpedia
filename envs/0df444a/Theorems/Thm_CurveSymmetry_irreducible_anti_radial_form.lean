-- Prove2me | Theorems.Thm_CurveSymmetry_irreducible_anti_radial_form
-- name    : CurveSymmetry.irreducible_anti_radial_form
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:42:21.859858+00:00
-- url     : https://prove2.me/theorems/b3aad4ac-12ad-4868-973c-d83f28029a18
-- title:
--   Irreducible conjugate-symmetric $P$ with $P(\zeta X,\zeta^{-1}Y)=-P$ equals $X^mA(XY)+Y^m\bar A(XY)$, $A$ nonconstant
-- statement:
--   Let $m\ge 2$ be an integer and let $\zeta\in\mathbb C$ be a primitive $2m$-th root of unity. Let $P(X,Y)=\sum_{a,b\ge 0}p_{ab}X^aY^b\in\mathbb C[X,Y]$ be an irreducible polynomial of total degree $d<2m$ whose coefficients are conjugate-symmetric, $p_{ba}=\overline{p_{ab}}$ for all $a,b\ge 0$, and which changes sign under $(X,Y)\mapsto(\zeta X,\zeta^{-1}Y)$, that is, $P(\zeta X,\zeta^{-1}Y)=-P(X,Y)$.
--
--   Then there is a polynomial $A\in\mathbb C[s]$ such that
--
--   $$
--   P(X,Y)=X^m\,A(XY)+Y^m\,\overline{A}(XY),
--   $$
--
--   where $\overline{A}$ is obtained from $A$ by conjugating its coefficients, and moreover:
--
--   1. $1\le\deg A\le\lfloor (d-m)/2\rfloor$;
--   2. $m+2\le d$.
--
--   This is the conclusion that the proof of Theorem 1 draws from equation (5): the polynomial $A$ is nonconstant, so $m\le d-2$, and a rotation of order $N=2m>d$ satisfies $N\le 2d-4$. The coefficient symmetry is the one of $P(X,Y)=f\big((X+Y)/2,(X-Y)/(2i)\big)$ for a real polynomial $f$; the version for real curves, recorded in the note as equation (5), is obtained from this statement.
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

theorem CurveSymmetry.irreducible_anti_radial_form {m : ℕ} (hm : 2 ≤ m) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * m)) {P : BPoly} (hirr : Irreducible P)
    (hdeg : P.totalDegree < 2 * m) (hanti : rotate ζ P = -P)
    (hreal : ∀ a b, P.coeff (exponent b a) = star (P.coeff (exponent a b))) :
    ∃ A : Polynomial ℂ,
      P = (X 0 : BPoly) ^ m * Polynomial.aeval ((X 0 : BPoly) * X 1) A +
        (X 1 : BPoly) ^ m * Polynomial.aeval ((X 0 : BPoly) * X 1) (A.map (starRingEnd ℂ)) ∧
      1 ≤ A.natDegree ∧ A.natDegree ≤ (P.totalDegree - m) / 2 ∧ m + 2 ≤ P.totalDegree := by sorry
