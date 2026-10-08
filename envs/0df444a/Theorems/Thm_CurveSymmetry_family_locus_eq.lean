-- Prove2me | Theorems.Thm_CurveSymmetry_family_locus_eq
-- name    : CurveSymmetry.family_locus_eq
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:40:25.789511+00:00
-- url     : https://prove2.me/theorems/f4db82e9-c16b-4e2b-8e2c-4c9691f0eb18
-- title:
--   The real locus of $P_\alpha$ is the curve $C_{m,\alpha}=\{z:\operatorname{Re}(z^m(|z|^2+\alpha))=0\}$
-- statement:
--   Let $m\ge0$ be an integer and $\alpha\in\mathbb C$ arbitrary. Let $P_\alpha(X,Y)=X^m(\alpha+XY)+Y^m(\bar\alpha+XY)\in\mathbb C[X,Y]$ be the polynomial of equation (6), and let $C_{m,\alpha}=\{z\in\mathbb C:\operatorname{Re}\bigl(z^m(|z|^2+\alpha)\bigr)=0\}$ be the set of equation (1).
--
--   Then the zero set of $P_\alpha$ in the complex coordinates $X=z$, $Y=\bar z$ is $C_{m,\alpha}$:
--   $$\{z\in\mathbb C: P_\alpha(z,\bar z)=0\}=C_{m,\alpha}.$$
--
--   This links the curves of the equality case of Theorem 1 with the polynomial $P_\alpha$ studied in Lemma 4, Theorem 2 and Remark 5. It holds for every $m$ and every $\alpha$, with no modulus or nonreality condition.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for Theorem 1, p. 1, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/PaperBounds.lean (C. Perassi)

import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Complex.OperatorNorm
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

theorem CurveSymmetry.family_locus_eq (m : ℕ) (α : ℂ) :
    realLocus (familyPolynomial m α) = extremalCurve m α := by sorry
