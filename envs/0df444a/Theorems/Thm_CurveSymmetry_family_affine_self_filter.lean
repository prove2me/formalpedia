-- Prove2me | Theorems.Thm_CurveSymmetry_family_affine_self_filter
-- name    : CurveSymmetry.family_affine_self_filter
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:41:00.512995+00:00
-- url     : https://prove2.me/theorems/69b22d16-bfe3-447b-9f42-8c78088b784f
-- title:
--   If $z\mapsto az+b$ with $a\ne0$ sends $C_{m,\alpha}$ into itself, then $b=0$ and $a^{2m}=1$
-- statement:
--   Let $m\ge 2$ be an integer, let $\alpha\in\mathbb{C}$ satisfy $|\alpha|=1$ and $\alpha\ne\bar\alpha$ (so $\alpha$ is not real), and let $C_{m,\alpha}=\{z\in\mathbb{C} : \operatorname{Re}\bigl(z^m(|z|^2+\alpha)\bigr)=0\}$. Let $a,b\in\mathbb{C}$ with $a\ne0$, and suppose that the affine map $z\mapsto az+b$ sends $C_{m,\alpha}$ into itself, that is, $az+b\in C_{m,\alpha}$ for every $z\in C_{m,\alpha}$.
--
--   Then
--
--   $$b=0\qquad\text{and}\qquad a^{2m}=1,$$
--
--   so the map is a rotation $z\mapsto az$ about the origin through an integer multiple of $\pi/m$. Only the inclusion is assumed, and $|a|=1$ is not assumed.
--
--   It treats the orientation-preserving maps in the description of the Euclidean symmetries of $C_{m,\alpha}$ in Theorem 2 of the note (the $2m$ rotations $z\mapsto cz$, $c^{2m}=1$, of equation (3)), and it is used to characterize the isometries of the plane that preserve $C_{m,\alpha}$. The quartic case $m=2$ is included.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note), Theorem 2, p. 2, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/FamilyEuclidean.lean (C. Perassi)

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
open OnePoint

theorem CurveSymmetry.family_affine_self_filter {m : ℕ} (hm : 2 ≤ m) {α a b : ℂ}
    (ha : α ≠ star α) (hα : ‖α‖ = 1) (ha0 : a ≠ 0)
    (hf : ∀ z ∈ extremalCurve m α, a * z + b ∈ extremalCurve m α) :
    b = 0 ∧ a ^ (2 * m) = 1 := by sorry
