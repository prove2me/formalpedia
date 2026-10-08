-- Prove2me | Theorems.Thm_CurveSymmetry_quintic_sixtyDegree_negates
-- name    : CurveSymmetry.quintic_sixtyDegree_negates
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:46:08.348302+00:00
-- url     : https://prove2.me/theorems/7dcb9cef-b9d7-47d0-bdc9-3dbfc43b63ec
-- title:
--   Rotation by $60^\circ$ negates the quintic $(x^2+y^2)(x^3-3xy^2)-3x^2y+y^3$
-- statement:
--   Let $f(x,y)=(x^2+y^2)(x^3-3xy^2)-3x^2y+y^3$, and for $z\in\mathbb{C}$ write $f(z)=f(\operatorname{Re}z,\operatorname{Im}z)$.
--
--   Then for every $z\in\mathbb{C}$,
--
--   $$f\bigl(e^{\pi i/3}z\bigr)=-f(z).$$
--
--   This is the identity stated with equation (2) of the note: the rotation through $60^\circ$ about the origin preserves the zero set of $f$ but multiplies $f$ by $-1$. It illustrates that a symmetry of a zero set need not fix its defining polynomial; in the notation of Lemma 3, this rotation has sign $\varepsilon=-1$.
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

theorem CurveSymmetry.quintic_sixtyDegree_negates (z : ℂ) :
    quinticValue (sixtyDegreeCoefficient * z) = -quinticValue z := by sorry
