-- Prove2me | Theorems.Thm_CurveSymmetry_family_branch_points
-- name    : CurveSymmetry.family_branch_points
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:41:44.649495+00:00
-- url     : https://prove2.me/theorems/3d688a17-627d-4394-8aa2-07761064e526
-- title:
--   The double cover $w^2=h_\alpha(t)$ has exactly $2m+2$ branch points: $\infty$ and the roots of $h_\alpha$
-- statement:
--   Let $m\ge 1$ be an integer and $\alpha\in\mathbb C$ with $\alpha\ne\bar\alpha$ (that is, $\alpha$ is not real), and let $h_\alpha(t)=-t\,(t^m+1)\,(\alpha t^m+\bar\alpha)\in\mathbb C[t]$. Let $L_\alpha=\mathbb C(t)[W]/(W^2-h_\alpha(t))$. For a point $p$ of the Riemann sphere $\mathbb C\cup\{\infty\}$, viewed as the $t$-line, a place of $L_\alpha$ over $p$ is a valuation subring $\mathcal O\ne L_\alpha$ of $L_\alpha$ containing $\mathbb C$ such that $t-c\in\mathcal O$ and $(t-c)^{-1}\notin\mathcal O$ if $p=c\in\mathbb C$, and such that $t\notin\mathcal O$ if $p=\infty$. Call $p$ a branch point if fewer than two places of $L_\alpha$ lie over $p$. Then:
--
--   1. the set of branch points is $\{\infty\}\cup\{c\in\mathbb C:\ h_\alpha(c)=0\}$;
--   2. there are exactly $2m+2$ branch points;
--   3. $\infty$ is a branch point;
--   4. $0$ is a branch point;
--   5. for every $c\in\mathbb C$ with $h_\alpha(c)\ne0$, exactly two places of $L_\alpha$ lie over $c$.
--
--   In short,
--
--   $$
--   \{\text{branch points}\}=\{\infty\}\cup\{c\in\mathbb C:\ h_\alpha(c)=0\},\qquad\big|\{\text{branch points}\}\big|=2m+2.
--   $$
--
--   This is the count of branch points of the double cover (7) in the proof of Lemma 4: exactly $2m+2$ of them, including $0$ and $\infty$. A branch point is defined here by its fibre (one place over the point instead of two); ramification indices are not part of the statement.
--
--   **Formalization Note**: the $t$-line is `OnePoint ℂ`, and the places over $p$ are counted with `Set.ncard` (which gives $0$ for an infinite set); $m>0$ and $\alpha\ne\bar\alpha$ are `Fact` instances.
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

theorem CurveSymmetry.family_branch_points :
    {p : OnePoint ℂ | IsFamilyBranchPoint m α p} =
        insert ∞ (((↑) : ℂ → OnePoint ℂ) '' ((familyH m α).roots.toFinset : Set ℂ)) ∧
      {p : OnePoint ℂ | IsFamilyBranchPoint m α p}.ncard = 2 * m + 2 ∧
      IsFamilyBranchPoint m α ∞ ∧ IsFamilyBranchPoint m α ((0 : ℂ) : OnePoint ℂ) ∧
      ∀ c : ℂ, (familyH m α).eval c ≠ 0 → (familyPlacesOver m α (c : OnePoint ℂ)).ncard = 2 := by sorry
