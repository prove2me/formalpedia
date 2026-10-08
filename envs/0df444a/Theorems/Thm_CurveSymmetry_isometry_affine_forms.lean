-- Prove2me | Theorems.Thm_CurveSymmetry_isometry_affine_forms
-- name    : CurveSymmetry.isometry_affine_forms
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:41:51.161878+00:00
-- url     : https://prove2.me/theorems/b312a30f-1e4d-4011-913e-e0570e5e94b9
-- title:
--   Every isometry of the plane is $z\mapsto az+b$ or $z\mapsto a\bar z+b$ with $|a|=1$
-- statement:
--   Identify the Euclidean plane with $\mathbb C$, with the distance $|z-w|$, and let $T:\mathbb C\to\mathbb C$ be a bijective isometry.
--
--   Then there exist $a,b\in\mathbb C$ with $|a|=1$ such that
--   $$T(z)=az+b\quad\text{for all }z\in\mathbb C\qquad\text{or}\qquad T(z)=a\bar z+b\quad\text{for all }z\in\mathbb C.$$
--
--   The maps $z\mapsto az+b$ are the rotations and translations, the maps $z\mapsto a\bar z+b$ the reflections and glide reflections. This classification lets the isometry groups $\mathrm{Sym}(C)$ and $\mathrm{Sym}^+(C)$ of a curve be handled through the complex affine formulas used in the note; it is used for Lemma 3 and for the counts of Euclidean symmetries in Theorems 1 and 2.
--
--   **Formalization Note**: isometries are elements of Mathlib's type `ℂ ≃ᵢ ℂ` of distance-preserving bijections of $\mathbb C$; no linearity is assumed.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, used for Theorem 1 (p. 1), Theorem 2 (p. 2), Lemma 3 (p. 2), https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/IsometryInterface.lean (C. Perassi)

import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Complex.Isometry
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

theorem CurveSymmetry.isometry_affine_forms (f : ℂ ≃ᵢ ℂ) :
    (∃ a b : ℂ, ‖a‖ = 1 ∧ ∀ z : ℂ, f z = a * z + b) ∨
    (∃ a b : ℂ, ‖a‖ = 1 ∧ ∀ z : ℂ, f z = a * star z + b) := by sorry
