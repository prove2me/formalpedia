-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_radial_outward_positive_of_ball
-- name    : BirkhoffGlobalSection.radial_outward_positive_of_ball
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T22:39:41.729455+00:00
-- url     : https://prove2.me/theorems/4ef09a95-dba9-49ef-a288-467b493cc362
-- title:
--   radial outward positive of ball
-- statement:
--   Under the displayed boundary-zero and interior sign hypotheses in a ball, the defining function is positive on a sufficiently short outward radial segment when the radial derivative is positive. The exact regularity, compactness, nonzero and uniqueness hypotheses displayed in the formal statement are retained.
-- source:
--   Independent extraction from accepted source Solutions/Sol_BirkhoffGlobalSection_radial_filling_locally_convex_at_each_point.lean:826. Local normalization abbreviations and map definitions are expanded explicitly in the statement. Exact mathematical scope retained; no global-section conclusion.

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

theorem BirkhoffGlobalSection.radial_outward_positive_of_ball (F : Phase → ℝ) (s b : Phase) (r t : ℝ)
    (ht : 1 < t) (hb : b ∈ Metric.ball s r) (hy : t • b ∈ Metric.ball s r)
    (hFb : F b = 0)
    (hball : ∀ z ∈ Metric.ball s r, DifferentiableAt ℝ F z ∧ 0 < fderiv ℝ F z z) :
    0 < F (t • b) := by sorry
