-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_inward_negative_second_derivative_boundary_not_stationary
-- name    : BirkhoffGlobalSection.inward_negative_second_derivative_boundary_not_stationary
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T22:39:40.976979+00:00
-- url     : https://prove2.me/theorems/c336302f-9cac-4a6a-aa42-4ac354b75dfa
-- title:
--   inward negative second derivative boundary not stationary
-- statement:
--   A continuous real function vanishing at one and strictly negative on [0,1) cannot have zero first derivative at one when its second total derivative there is positive. The exact regularity, compactness, nonzero and uniqueness hypotheses displayed in the formal statement are retained.
-- source:
--   Independent extraction from accepted source Solutions/Sol_BirkhoffGlobalSection_radial_filling_locally_convex_at_each_point.lean:202. Local normalization abbreviations and map definitions are expanded explicitly in the statement. Exact mathematical scope retained; no global-section conclusion.

import Definitions.Def_BirkhoffGlobalSection
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue


open BirkhoffGlobalSection


open BirkhoffGlobalSection NormedSpace Set Metric Filter
open scoped Topology unitInterval BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

theorem BirkhoffGlobalSection.inward_negative_second_derivative_boundary_not_stationary (f : ℝ → ℝ)
    (hc : ContinuousAt f 1) (hzero : f 1 = 0)
    (hneg : ∀ t : ℝ, 0 ≤ t → t < 1 → f t < 0)
    (hsecond : 0 < deriv (deriv f) 1) : deriv f 1 ≠ 0 := by sorry
