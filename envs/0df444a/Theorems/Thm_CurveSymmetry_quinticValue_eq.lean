-- Prove2me | Theorems.Thm_CurveSymmetry_quinticValue_eq
-- name    : CurveSymmetry.quinticValue_eq
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:46:07.32775+00:00
-- url     : https://prove2.me/theorems/5d8784da-49c6-40cd-8d5f-e91e1ffc4a72
-- title:
--   The quintic $(x^2+y^2)(x^3-3xy^2)-3x^2y+y^3$ equals $\operatorname{Re}\bigl(z^3(|z|^2+i)\bigr)$
-- statement:
--   Let $f\in\mathbb{R}[x,y]$ be the quintic polynomial $f(x,y)=(x^2+y^2)(x^3-3xy^2)-3x^2y+y^3$, and identify $\mathbb{R}^2$ with $\mathbb{C}$ through $z=x+iy$.
--
--   Then for every $z\in\mathbb{C}$,
--
--   $$f(\operatorname{Re}z,\operatorname{Im}z)=\operatorname{Re}\bigl(z^3(|z|^2+i)\bigr).$$
--
--   This is the identity of equation (2) of the note. It writes the quintic in the form $\operatorname{Re}\bigl(z^m(|z|^2+\alpha)\bigr)$ of the family (1), with $m=3$ and $\alpha=i$; the note uses this quintic as an irreducible curve with a rotation of order six that changes the sign of its equation.
--
--   **Formalization Note**: The quintic is encoded as a real-valued function of $z\in\mathbb{C}$: the printed Cartesian expression evaluated at $x=\operatorname{Re}z$, $y=\operatorname{Im}z$.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note), equation (2), p. 1, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/QuinticExample.lean (C. Perassi)

import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_04_ProjectiveClosure
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
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
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

open CurveSymmetry
set_option autoImplicit false

theorem CurveSymmetry.quinticValue_eq (z : ℂ) :
    quinticValue z = (z ^ 3 * ((‖z‖ : ℂ) ^ 2 + Complex.I)).re := by sorry
