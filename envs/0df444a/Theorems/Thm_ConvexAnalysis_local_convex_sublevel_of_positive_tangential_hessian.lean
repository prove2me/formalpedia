-- Prove2me | Theorems.Thm_ConvexAnalysis_local_convex_sublevel_of_positive_tangential_hessian
-- name    : ConvexAnalysis.local_convex_sublevel_of_positive_tangential_hessian
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-30T00:10:37.788026+00:00
-- url     : https://prove2.me/theorems/9c067eda-8d74-4593-9fe5-aa23299f9227
-- title:
--   Positive tangential Hessian gives a locally convex sublevel
-- statement:
--   Let E be a proper real normed vector space and F:E to R be C2 at a point s with F(s)=0. Suppose
--   $$v\ne0,\ DF(s)[v]=0\quad\Longrightarrow\quad D^2F(s)[v,v]>0.$$
--   Then s has a neighborhood U for which
--   $$\{x:F(x)\le0\}\cap U\quad\text{is convex}.$$
--   This is a local convexity criterion for the inward side of a level set. A separate nonvanishing derivative hypothesis is not required, and no radial structure is assumed.
-- source:
--   Original normed-space generalization of helper 'local_convex_sublevel_of_positive_tangential_hessian' in the accepted proof of BirkhoffGlobalSection.radial_filling_locally_convex_at_each_point, submission 0e9512c6-f3a9-4bf7-9a12-f44fda8605af, https://prove2.me/api/v1/submissions/0e9512c6-f3a9-4bf7-9a12-f44fda8605af/solution. This is an extracted supporting theorem, not a verbatim statement from Joung--van Koert.

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

theorem ConvexAnalysis.local_convex_sublevel_of_positive_tangential_hessian {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] (F : E → ℝ) (s : E)
    (hc : ContDiffAt ℝ 2 F s) (hz : F s = 0)
    (htan : ∀ v : E, v ≠ 0 → fderiv ℝ F s v = 0 →
      0 < fderiv ℝ (fun x => fderiv ℝ F x v) s v) :
    ∃ U : Set E, U ∈ nhds s ∧ Convex ℝ ({y | F y ≤ 0} ∩ U) := by sorry
