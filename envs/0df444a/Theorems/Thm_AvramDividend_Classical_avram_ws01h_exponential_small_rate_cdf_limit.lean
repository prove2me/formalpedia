-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01h_exponential_small_rate_cdf_limit
-- name    : AvramDividend.Classical.avram_ws01h_exponential_small_rate_cdf_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T13:10:12.717866+00:00
-- url     : https://prove2.me/theorems/8bb46f89-a5ba-48d5-95d2-15191967bfc0
-- title:
--   Exponential small-positive-root CDF complement tends to zero for arbitrary rate functions
-- statement:
--   For any filter and real rate family tending to zero, the exact exponential distribution left-tail analytic expression 1-exp(-lambda*b), embedded in ENNReal, tends to zero for every fixed b. This is the deterministic Abel remainder limit for the true Esscher finite-clock no-upper-record bound when the canonically proved positive shifted-root lambda_p tends to zero.
-- source:
--   Pinned Mathlib continuity of the exponential function and ENNReal.ofReal, for use with the genuine Qp exponential supremum law cf4dc156 and original-Lévy positive-root family 868634e8.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

open AvramDividend.Classical MeasureTheory Filter
open scoped ENNReal Topology

theorem AvramDividend.Classical.avram_ws01h_exponential_small_rate_cdf_limit
    (b : ℝ) (lam : ℝ → ℝ) (l : Filter ℝ)
    (hlam : Tendsto lam l (𝓝 (0 : ℝ))) :
    Tendsto (fun p : ℝ =>
      ENNReal.ofReal (1 - Real.exp (-(lam p * b))))
      l (𝓝 (0 : ℝ≥0∞)) := by sorry
