-- Prove2me | Theorems.Thm_CurveSymmetry_familyH_roots_card
-- name    : CurveSymmetry.familyH_roots_card
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:41:23.794811+00:00
-- url     : https://prove2.me/theorems/da468318-cb31-4cc3-ad66-036368fe64ee
-- title:
--   The polynomial $h_\alpha(t)=-t(t^m+1)(\alpha t^m+\bar\alpha)$ has exactly $2m+1$ distinct roots
-- statement:
--   Let $m\ge 1$ be an integer and $\alpha\in\mathbb C$ with $\alpha\ne\bar\alpha$, and let $h_\alpha(t)=-t\,(t^m+1)\,(\alpha t^m+\bar\alpha)\in\mathbb C[t]$. Then the number of distinct complex roots of $h_\alpha$ is
--
--   $$
--   \big|\{c\in\mathbb C:\ h_\alpha(c)=0\}\big|=2m+1.
--   $$
--
--   The roots of $h_\alpha$ are the finite branch points of the double cover (7) in the proof of Lemma 4; together with $\infty$ they give its $2m+2$ branch points.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note), proof of Lemma 4, p. 4, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/FamilyBranchPoints.lean (C. Perassi)

import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
import Definitions.Def_CurveSymmetry_06_QuadraticRing
import Definitions.Def_CurveSymmetry_07_Places
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Tactic
import Mathlib.Topology.Compactification.OnePoint.Basic

open CurveSymmetry
set_option autoImplicit false
open Polynomial OnePoint
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
omit hm ha

theorem CurveSymmetry.familyH_roots_card (hm0 : 0 < m) (hα : α ≠ star α) :
    (familyH m α).roots.toFinset.card = 2 * m + 1 := by sorry
