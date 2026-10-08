-- Prove2me | Theorems.Thm_CurveSymmetry_family_no_conjugate_affine
-- name    : CurveSymmetry.family_no_conjugate_affine
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:40:35.207951+00:00
-- url     : https://prove2.me/theorems/abf462dd-31b7-49a0-a8a4-2a71cc26bfcd
-- title:
--   No map $z\mapsto a\bar z+b$ with $a\ne0$ sends $C_{m,\alpha}$ into itself
-- statement:
--   Let $m\ge 2$ be an integer, let $\alpha\in\mathbb{C}$ satisfy $|\alpha|=1$ and $\alpha\ne\bar\alpha$ (so $\alpha$ is not real), and let $C_{m,\alpha}=\{z\in\mathbb{C} : \operatorname{Re}\bigl(z^m(|z|^2+\alpha)\bigr)=0\}$. Let $a,b\in\mathbb{C}$ with $a\ne0$, and consider the conjugate-affine map $z\mapsto a\bar z+b$.
--
--   Then this map does not send $C_{m,\alpha}$ into itself:
--
--   $$\{\,a\bar z+b : z\in C_{m,\alpha}\,\}\not\subseteq C_{m,\alpha},$$
--
--   that is, $a\bar z+b\notin C_{m,\alpha}$ for some $z\in C_{m,\alpha}$. Even the inclusion is excluded, not only equality of sets, and $|a|$ is arbitrary, so the map need not be an isometry.
--
--   Since every orientation-reversing isometry of the plane has the form $z\mapsto a\bar z+b$ with $|a|=1$, this shows that $C_{m,\alpha}$ has no reflection or glide-reflection symmetry: it is the orientation-reversing part of the claim in Theorem 2 of the note that the Euclidean symmetries of $C_{m,\alpha}$ are rotations. It also serves Theorem 1, where the curves $C_{d-2,i}$ with $d\ge4$ attain the rotation bound. The quartic case $m=2$ is included.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for Theorem 2, p. 2; proof of Theorem 2, p. 4, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/FamilyEuclidean.lean (C. Perassi)

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

theorem CurveSymmetry.family_no_conjugate_affine {m : ℕ} (hm : 2 ≤ m) {α a b : ℂ}
    (ha : α ≠ star α) (hα : ‖α‖ = 1) (ha0 : a ≠ 0) :
    ¬ (∀ z ∈ extremalCurve m α, a * star z + b ∈ extremalCurve m α) := by sorry
