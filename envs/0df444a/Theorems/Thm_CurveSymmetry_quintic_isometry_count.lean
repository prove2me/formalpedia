-- Prove2me | Theorems.Thm_CurveSymmetry_quintic_isometry_count
-- name    : CurveSymmetry.quintic_isometry_count
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:46:04.742791+00:00
-- url     : https://prove2.me/theorems/e5a8bd7d-a2a0-4797-b9b0-cba45c9dd8ee
-- title:
--   The quintic curve $(x^2+y^2)(x^3-3xy^2)-3x^2y+y^3=0$ has exactly six Euclidean symmetries
-- statement:
--   Let $f(x,y)=(x^2+y^2)(x^3-3xy^2)-3x^2y+y^3$, identify $\mathbb{R}^2$ with $\mathbb{C}$ through $z=x+iy$, and let $C=\{z\in\mathbb{C} : f(\operatorname{Re}z,\operatorname{Im}z)=0\}$ be the real zero set. Let $\mathrm{Sym}(C)$ be the group of all isometries $T$ of the Euclidean plane, orientation-preserving or not, with $T(z)\in C\iff z\in C$ for every $z\in\mathbb{C}$.
--
--   Then $\mathrm{Sym}(C)$ is finite and
--
--   $$|\mathrm{Sym}(C)|=6.$$
--
--   This is the count stated with equation (2) of the note, that the quintic has exactly six rotations. Since the rotation $z\mapsto e^{\pi i/3}z$ preserves $C$ and has order six, the six symmetries are the rotations about the origin through multiples of $60^\circ$; in particular $C$ has no reflection symmetry.
--
--   **Formalization Note**: $\mathrm{Sym}(C)$ is the subgroup of the isometries `ℂ ≃ᵢ ℂ` preserving $C$, and the count is `Nat.card`.
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

theorem CurveSymmetry.quintic_isometry_count :
    Nat.card (isometrySetGroup {z : ℂ | quinticValue z = 0}) = 6 := by sorry
