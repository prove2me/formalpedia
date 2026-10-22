-- Prove2me | Theorems.Thm_ConvexAnalysis_local_max_second_derivative_nonpositive
-- name    : ConvexAnalysis.local_max_second_derivative_nonpositive
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T22:00:34.44199+00:00
-- url     : https://prove2.me/theorems/da44c410-d024-435c-bc68-b0522853699a
-- title:
--   Local max second derivative nonpositive
-- statement:
--   At a local maximum of a real function continuous at that point, the second total derivative is nonpositive. The statement uses Lean total derivatives and does not assume their existence separately.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Original auxiliary result from the accepted source Solutions/Sol_ConvexAnalysis_convex_frontier_radial_derivative_positive.lean:119. Exact quantified statement retained; foundational calculus and geometry are imported from Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Definitions.Def_BirkhoffGlobalSection_ConvexRegularizationModel
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.LocallyConvex.Separation
import Theorems.Thm_ConvexAnalysis_convex_frontier_radial_derivative_ne_zero
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.ContDiff.Deriv

open BirkhoffGlobalSection ConvexAnalysis Filter Set
open scoped ContDiff Topology


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem ConvexAnalysis.local_max_second_derivative_nonpositive (f : ℝ → ℝ) (x : ℝ)
    (hmax : IsLocalMax f x) (hc : ContinuousAt f x) : deriv (deriv f) x ≤ 0 := by sorry
