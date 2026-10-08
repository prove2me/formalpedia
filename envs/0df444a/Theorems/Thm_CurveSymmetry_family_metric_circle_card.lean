-- Prove2me | Theorems.Thm_CurveSymmetry_family_metric_circle_card
-- name    : CurveSymmetry.family_metric_circle_card
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:41:23.121731+00:00
-- url     : https://prove2.me/theorems/1747f2f0-e788-449b-9f76-2ce0c866816b
-- title:
--   Every circle $|z|=r$ with $r>0$ meets $C_{m,\alpha}$ in exactly $2m$ points
-- statement:
--   Let $m\ge 1$ be an integer, let $\alpha\in\mathbb{C}$ be nonreal, $\alpha\ne\bar\alpha$ (no condition on $|\alpha|$), and let $C_{m,\alpha}=\{z\in\mathbb{C} : \operatorname{Re}\bigl(z^m(|z|^2+\alpha)\bigr)=0\}$. Let $r>0$ be a real number.
--
--   Then the circle of radius $r$ centered at the origin meets $C_{m,\alpha}$ in a finite set of exactly $2m$ points:
--
--   $$\#\bigl(C_{m,\alpha}\cap\{z\in\mathbb{C} : |z|=r\}\bigr)=2m.$$
--
--   In the proof of Lemma 4 of the note, this count is what shows that $C_{m,\alpha}$ is infinite.
--
--   **Formalization Note**: The circle is the metric sphere of radius $r$ about $0$ in $\mathbb{C}$, and the count is `Nat.card` of the intersection, so finiteness is part of the statement.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note), proof of Lemma 4, p. 4, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/FamilyCircleSections.lean (C. Perassi)

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

theorem CurveSymmetry.family_metric_circle_card {m : ℕ} (hm : 0 < m) {α : ℂ}
    (ha : α ≠ star α) {r : ℝ} (hr : 0 < r) :
    Nat.card ↥(extremalCurve m α ∩ Metric.sphere (0 : ℂ) r) = 2 * m := by sorry
