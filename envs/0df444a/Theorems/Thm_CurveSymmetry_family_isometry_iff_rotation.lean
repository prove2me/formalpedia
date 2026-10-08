-- Prove2me | Theorems.Thm_CurveSymmetry_family_isometry_iff_rotation
-- name    : CurveSymmetry.family_isometry_iff_rotation
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:42:17.131588+00:00
-- url     : https://prove2.me/theorems/abe99453-76b5-4e22-829d-b7ad486948e5
-- title:
--   An isometry of $\mathbb{C}$ preserves $C_{m,\alpha}$ if and only if it is a rotation $z\mapsto cz$ with $c^{2m}=1$
-- statement:
--   Let $m\ge 2$ be an integer, let $\alpha\in\mathbb{C}$ satisfy $|\alpha|=1$ and $\alpha\ne\bar\alpha$ (so $\alpha$ is not real), and let $C_{m,\alpha}=\{z\in\mathbb{C} : \operatorname{Re}\bigl(z^m(|z|^2+\alpha)\bigr)=0\}$. Let $T:\mathbb{C}\to\mathbb{C}$ be an isometry of the Euclidean plane, that is, a distance-preserving bijection.
--
--   Then $T$ preserves $C_{m,\alpha}$ exactly when it is a rotation about the origin whose coefficient is a $2m$-th root of unity:
--
--   $$\bigl(\forall z\in\mathbb{C}:\ T(z)\in C_{m,\alpha}\iff z\in C_{m,\alpha}\bigr)\iff\exists\,c\in\mathbb{C}:\ c^{2m}=1\ \text{ and }\ T(z)=cz\ \text{ for all } z\in\mathbb{C}.$$
--
--   This is the description of the Euclidean symmetry group in Theorem 2 of the note: it consists of the $2m$ rotations $z\mapsto cz$, $c^{2m}=1$, of equation (3). The quartic case $m=2$ is included.
--
--   **Formalization Note**: $T$ is an isometric equivalence `ℂ ≃ᵢ ℂ`.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note), proof of Theorem 2, p. 4, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/FamilyEuclidean.lean (C. Perassi)

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

theorem CurveSymmetry.family_isometry_iff_rotation {m : ℕ} (hm : 2 ≤ m) {α : ℂ}
    (ha : α ≠ star α) (hα : ‖α‖ = 1) (f : ℂ ≃ᵢ ℂ) :
    (∀ z, f z ∈ extremalCurve m α ↔ z ∈ extremalCurve m α) ↔
      ∃ a : ℂ, a ^ (2 * m) = 1 ∧ ∀ z, f z = a * z := by sorry
