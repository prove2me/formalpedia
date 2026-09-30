-- Prove2me | Theorems.Thm_ConvexAnalysis_quadratic_rank_one_correction
-- name    : ConvexAnalysis.quadratic_rank_one_correction
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-30T00:10:07.35498+00:00
-- url     : https://prove2.me/theorems/a18c6f9f-50df-4145-ab84-4259240fc8a6
-- title:
--   Positive rank-one correction of a homogeneous quadratic function
-- statement:
--   Let E be a proper real normed vector space, L a continuous linear functional on E, and q a continuous function homogeneous of degree two. Suppose q(v)>0 for every nonzero v in the kernel of L. Then
--   $$\exists c>0\quad\forall v\ne0,\qquad q(v)+cL(v)^2>0.$$
--   This separates tangential positivity from a full positivity certificate. Properness supplies compact norm spheres; in particular the result applies to every finite-dimensional real normed space. The function q need not be specified by a symmetric bilinear form.
-- source:
--   Original normed-space generalization of helper 'finite_dimensional_quadratic_correction' in the accepted proof of BirkhoffGlobalSection.radial_filling_locally_convex_at_each_point, submission 0e9512c6-f3a9-4bf7-9a12-f44fda8605af, https://prove2.me/api/v1/submissions/0e9512c6-f3a9-4bf7-9a12-f44fda8605af/solution. This is an extracted supporting theorem, not a verbatim statement from Joung--van Koert.

import Mathlib.Tactic.Abel
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.NormNum
open NormedSpace
open scoped Topology
open scoped Topology

theorem ConvexAnalysis.quadratic_rank_one_correction {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] (L : E →L[ℝ] ℝ) (q : E → ℝ)
    (hq : Continuous q) (hhom : ∀ r : ℝ, ∀ v : E, q (r • v) = r ^ 2 * q v)
    (htan : ∀ v : E, v ≠ 0 → L v = 0 → 0 < q v) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : E, v ≠ 0 → 0 < q v + c * (L v) ^ 2 := by sorry
