-- Prove2me | Theorems.Thm_CurveSymmetry_sixtyDegree_isometry_order
-- name    : CurveSymmetry.sixtyDegree_isometry_order
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:46:33.331253+00:00
-- url     : https://prove2.me/theorems/08fdbd54-9326-4777-98cd-6721db3e2b35
-- title:
--   The rotation $z\mapsto e^{\pi i/3}z$ has order exactly $6$ in the isometry group of the plane
-- statement:
--   Let $\rho:\mathbb{C}\to\mathbb{C}$, $\rho(z)=e^{\pi i/3}z$, be the rotation through $60^\circ$ about the origin, regarded as an element of the group of isometries of the Euclidean plane $\mathbb{C}$ under composition.
--
--   Then
--
--   $$\operatorname{ord}(\rho)=6,$$
--
--   that is, $\rho^6=\mathrm{id}$ and $\rho^k\ne\mathrm{id}$ for $1\le k\le5$.
--
--   This is the rotation of order six in the quintic example of equation (2) of the note. The statement concerns the isometry itself, not only its coefficient $e^{\pi i/3}$ as a root of unity.
--
--   **Formalization Note**: $\rho$ is the affine isometry $z\mapsto az+b$ with $a=e^{\pi i/3}$, of modulus one, and $b=0$, as an element of the group `ℂ ≃ᵢ ℂ`.
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

theorem CurveSymmetry.sixtyDegree_isometry_order :
    orderOf (affineDirectIsometry sixtyDegreeCoefficient 0 sixtyDegree_norm) = 6 := by sorry
