-- Prove2me | Theorems.Thm_ConvexAnalysis_positive_hessian_neighborhood
-- name    : ConvexAnalysis.positive_hessian_neighborhood
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-30T00:10:18.134128+00:00
-- url     : https://prove2.me/theorems/460a73c7-2bd3-4ecc-b956-87cbc1fe60d1
-- title:
--   Positive Hessian persists on a neighborhood
-- statement:
--   Let E be a proper real normed vector space and F:E to R be C2 at s. If its Hessian is positive on every nonzero vector at s, then there is a positive radius r such that F is C2 at every point of the ball and
--   $$\forall x\in B(s,r)\ \forall v\ne0,\qquad D^2F(x)[v,v]>0.$$
--   This supplies a uniform neighborhood on which positive definiteness holds simultaneously in every direction. It is independent of an inner-product choice.
-- source:
--   Original normed-space generalization of helper 'positive_hessian_neighborhood' in the accepted proof of BirkhoffGlobalSection.radial_filling_locally_convex_at_each_point, submission 0e9512c6-f3a9-4bf7-9a12-f44fda8605af, https://prove2.me/api/v1/submissions/0e9512c6-f3a9-4bf7-9a12-f44fda8605af/solution. This is an extracted supporting theorem, not a verbatim statement from Joung--van Koert.

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

theorem ConvexAnalysis.positive_hessian_neighborhood {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] (F : E → ℝ) (s : E)
    (hc : ContDiffAt ℝ 2 F s)
    (hpos : ∀ v : E, v ≠ 0 → 0 < fderiv ℝ (fun z => fderiv ℝ F z v) s v) :
    ∃ r > 0, ∀ x ∈ Metric.ball s r, ContDiffAt ℝ 2 F x ∧
      ∀ v : E, v ≠ 0 → 0 < fderiv ℝ (fun z => fderiv ℝ F z v) x v := by sorry
