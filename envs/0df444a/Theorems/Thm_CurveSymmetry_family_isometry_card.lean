-- Prove2me | Theorems.Thm_CurveSymmetry_family_isometry_card
-- name    : CurveSymmetry.family_isometry_card
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:40:45.666765+00:00
-- url     : https://prove2.me/theorems/316f3f50-f66c-41e5-b93a-9b857082e22e
-- title:
--   The Euclidean symmetry group of $C_{m,\alpha}$ has exactly $2m$ elements
-- statement:
--   Let $m\ge 2$ be an integer, let $\alpha\in\mathbb{C}$ satisfy $|\alpha|=1$ and $\alpha\ne\bar\alpha$ (so $\alpha$ is not real), and let $C_{m,\alpha}=\{z\in\mathbb{C} : \operatorname{Re}\bigl(z^m(|z|^2+\alpha)\bigr)=0\}$. Let $\mathrm{Sym}(C_{m,\alpha})$ be the group of all isometries $T$ of the Euclidean plane $\mathbb{C}$, orientation-preserving or not, with $T(z)\in C_{m,\alpha}\iff z\in C_{m,\alpha}$ for every $z\in\mathbb{C}$.
--
--   Then $\mathrm{Sym}(C_{m,\alpha})$ is finite and
--
--   $$|\mathrm{Sym}(C_{m,\alpha})|=2m.$$
--
--   This is the count of Euclidean symmetries in Theorem 2 of the note, where they are the $2m$ rotations $z\mapsto cz$, $c^{2m}=1$, of equation (3). It supports Theorem 1, whose rotation bound $2d-4$ is attained by the curves $C_{d-2,i}$ for $d\ge4$, and it is used to count the symmetries of the quintic (2).
--
--   **Formalization Note**: The group is the subgroup of the isometries `ℂ ≃ᵢ ℂ` preserving the set $C_{m,\alpha}$, and the cardinality is `Nat.card`, so the statement includes finiteness.
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

theorem CurveSymmetry.family_isometry_card {m : ℕ} (hm : 2 ≤ m) {α : ℂ}
    (ha : α ≠ star α) (hα : ‖α‖ = 1) :
    Nat.card (isometrySetGroup (extremalCurve m α)) = 2 * m := by sorry
