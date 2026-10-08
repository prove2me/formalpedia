-- Prove2me | Theorems.Thm_CurveSymmetry_family_degreeOf
-- name    : CurveSymmetry.family_degreeOf
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:40:46.014155+00:00
-- url     : https://prove2.me/theorems/df85128c-7a88-41fd-9f48-52aafa7a0dbc
-- title:
--   $P_\alpha=X^m(\alpha+XY)+Y^m(\bar\alpha+XY)$ has degree exactly $m+1$ in each variable
-- statement:
--   Let $m\ge1$ be an integer and let $\alpha\in\mathbb C$ be arbitrary. Consider the polynomial of equation (6), $P_\alpha(X,Y)=X^m(\alpha+XY)+Y^m(\bar\alpha+XY)\in\mathbb C[X,Y]$; in the coordinates $X=z$, $Y=\bar z$ it satisfies $P_\alpha(z,\bar z)=2\operatorname{Re}\bigl(z^m(|z|^2+\alpha)\bigr)$.
--
--   Then the degree of $P_\alpha$ in each of the two variables separately equals $m+1$:
--
--   $$
--   \deg_X P_\alpha=\deg_Y P_\alpha=m+1.
--   $$
--
--   This is the degree count behind the statement after equation (6) that the closure $V_\alpha$ of the curve $P_\alpha=0$ in $\mathbb P^1\times\mathbb P^1$ has bidegree $(m+1,m+1)$. In the formalization these separate degree bounds, rather than a bound on the total degree, show that a nonzero polynomial divisible by $P_\alpha$ and of degree at most $m+1$ in each variable is a scalar multiple of $P_\alpha$; this gives the proportionality of Möbius pullbacks used in the proof of Theorem 2.
--
--   **Formalization Note**: the degree in one variable is Mathlib's `MvPolynomial.degreeOf`, and the statement is made for both variables of `MvPolynomial (Fin 2) ℂ`.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note), Section 3, closure of equation (6), p. 3, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/FamilyBidegree.lean (C. Perassi)

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
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

open CurveSymmetry
set_option autoImplicit false
open MvPolynomial
open OnePoint

theorem CurveSymmetry.family_degreeOf {m : ℕ} (hm : 0 < m) (α : ℂ) (i : Fin 2) :
    (familyPolynomial m α).degreeOf i = m + 1 := by sorry
