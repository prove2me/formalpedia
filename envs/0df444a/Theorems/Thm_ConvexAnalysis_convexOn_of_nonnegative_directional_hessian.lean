-- Prove2me | Theorems.Thm_ConvexAnalysis_convexOn_of_nonnegative_directional_hessian
-- name    : ConvexAnalysis.convexOn_of_nonnegative_directional_hessian
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-30T00:10:21.927039+00:00
-- url     : https://prove2.me/theorems/79c8fc93-99b2-4e1f-88e5-7cce6a8bc618
-- title:
--   A nonnegative directional Hessian implies convexity
-- statement:
--   Let E be a real normed vector space, U a convex subset, and F:E to R be C2 at every point of U. If
--   $$\forall x\in U\ \forall v\in E,\qquad D^2F(x)[v,v]\ge0,$$
--   then F is convex on U. This converts directional second-derivative estimates into a convexity assertion and applies in arbitrary dimension. The C2 hypothesis is ambient at every point, even if U has empty interior.
-- source:
--   Original normed-space generalization of helper 'convexOn_of_nonnegative_directional_hessian' in the accepted proof of BirkhoffGlobalSection.radial_filling_locally_convex_at_each_point, submission 0e9512c6-f3a9-4bf7-9a12-f44fda8605af, https://prove2.me/api/v1/submissions/0e9512c6-f3a9-4bf7-9a12-f44fda8605af/solution. This is an extracted supporting theorem, not a verbatim statement from Joung--van Koert.

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

theorem ConvexAnalysis.convexOn_of_nonnegative_directional_hessian {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : E → ℝ) (U : Set E)
    (hU : Convex ℝ U) (hc : ∀ x ∈ U, ContDiffAt ℝ 2 F x)
    (hpos : ∀ x ∈ U, ∀ v : E, 0 ≤ fderiv ℝ (fun z => fderiv ℝ F z v) x v) :
    ConvexOn ℝ U F := by sorry
