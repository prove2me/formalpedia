-- Prove2me | Theorems.Thm_CurveSymmetry_sphericalFamily_eq
-- name    : CurveSymmetry.sphericalFamily_eq
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:46:10.639224+00:00
-- url     : https://prove2.me/theorems/758b12ee-ecda-4929-a1a4-fe3112099c7a
-- title:
--   The spherical closure $\widehat C_{m,\alpha}$ equals $C_{m,\alpha}\cup\{\infty\}$ for every nonreal $\alpha$
-- statement:
--   Let $m\ge1$ be an integer and let $\alpha\in\mathbb C$ with $\alpha\notin\mathbb R$; no condition is imposed on $|\alpha|$. Let $C_{m,\alpha}=\{z\in\mathbb C:\operatorname{Re}\bigl(z^m(|z|^2+\alpha)\bigr)=0\}$ as in equation (1), and let $\widehat C_{m,\alpha}$ be the closure of $C_{m,\alpha}$ in the Riemann sphere $\widehat{\mathbb C}=\mathbb C\cup\{\infty\}$, the one-point compactification of $\mathbb C$.
--
--   Then
--   $$\widehat C_{m,\alpha}=C_{m,\alpha}\cup\{\infty\}.$$
--
--   It describes the curve $\widehat C_{m,\alpha}$ on which the Möbius statements of Theorem 2 and Remark 5 are made: taking the closure adds exactly the point at infinity and no finite point.
--
--   **Formalization Note**: the Riemann sphere is `OnePoint ℂ` with its usual topology, $C_{m,\alpha}$ enters through the inclusion $\mathbb C\hookrightarrow\widehat{\mathbb C}$, and the closure is the topological closure there.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, used for Theorem 1 (p. 1), Theorem 2 (p. 2), Lemma 4 (p. 3), https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/SphereGeometry.lean (C. Perassi)

import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Complex.OperatorNorm
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
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

open CurveSymmetry
set_option autoImplicit false
open scoped LinearAlgebra.Projectivization
open OnePoint

theorem CurveSymmetry.sphericalFamily_eq {m : ℕ} (hm : 0 < m) {α : ℂ} (ha : α ≠ star α) :
    sphericalFamily m α = insert ∞ (((↑) : ℂ → Sphere) '' extremalCurve m α) := by sorry
