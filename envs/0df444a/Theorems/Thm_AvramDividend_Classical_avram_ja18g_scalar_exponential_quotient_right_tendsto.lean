-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18g_scalar_exponential_quotient_right_tendsto
-- name    : AvramDividend.Classical.avram_ja18g_scalar_exponential_quotient_right_tendsto
-- status  : Open
-- author  : @WillR
-- created : 2026-11-11T04:07:42.896201+00:00
-- url     : https://prove2.me/theorems/8d050fdd-b9cd-41d8-ac28-ef661bb10ea8
-- title:
--   Scalar exponential quotient tends to its input from the right at zero
-- statement:
--   For each real x, the positive-parameter quotient (exp(theta*x)-1)/theta tends to x as theta tends to zero from above. Derive this from the chain rule and the right slope of exp, independent of stochastic hypotheses.
-- source:
--   J-A18 original Levy Laplace first-moment derivative elementary child

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18g_scalar_exponential_quotient_right_tendsto
    (x : ℝ) :
    Filter.Tendsto (fun θ : ℝ => (Real.exp (θ * x) - 1) / θ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds x) := by sorry
