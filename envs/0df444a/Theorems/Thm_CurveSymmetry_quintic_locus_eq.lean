-- Prove2me | Theorems.Thm_CurveSymmetry_quintic_locus_eq
-- name    : CurveSymmetry.quintic_locus_eq
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:46:05.620014+00:00
-- url     : https://prove2.me/theorems/27ed52fa-9b83-43d1-83b8-314bcbad4805
-- title:
--   The zero set of the quintic $(x^2+y^2)(x^3-3xy^2)-3x^2y+y^3$ is the curve $C_{3,i}$
-- statement:
--   Let $f(x,y)=(x^2+y^2)(x^3-3xy^2)-3x^2y+y^3$, identify $\mathbb{R}^2$ with $\mathbb{C}$ through $z=x+iy$, and let $C_{3,i}$ be the member $m=3$, $\alpha=i$ of the family $C_{m,\alpha}=\{z\in\mathbb{C} : \operatorname{Re}\bigl(z^m(|z|^2+\alpha)\bigr)=0\}$.
--
--   Then the real zero set of $f$ is $C_{3,i}$:
--
--   $$\{z\in\mathbb{C} : f(\operatorname{Re}z,\operatorname{Im}z)=0\}=\{z\in\mathbb{C} : \operatorname{Re}\bigl(z^3(|z|^2+i)\bigr)=0\}=C_{3,i}.$$
--
--   It identifies the quintic of equation (2) of the note with a member of the family (1), so that the results on the family (Lemma 4, Theorem 2) apply to it; it is used to count the symmetries of the quintic.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for equation (2), p. 1, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/QuinticExample.lean (C. Perassi)

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

theorem CurveSymmetry.quintic_locus_eq :
    {z : ℂ | quinticValue z = 0} = extremalCurve 3 Complex.I := by sorry
