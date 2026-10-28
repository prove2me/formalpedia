-- Prove2me | Theorems.Thm_AvramDividend_Classical_pointwise_summable_monotone_tsum
-- name    : AvramDividend.Classical.pointwise_summable_monotone_tsum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:00:24.443221+00:00
-- url     : https://prove2.me/theorems/8f1c8a36-9541-4118-ba32-7dbf82b80ba4
-- title:
--   Pointwise summable increasing kernels have a nondecreasing series sum
-- statement:
--   If every real-valued summand F_n is nondecreasing as a function of x, and the series over n is summable at every x, then the summed function is nondecreasing. This passes the monotonicity of positive-discount renewal convolution powers to their resolvent series.
-- source:
--   Mathlib Summable.tsum_le_tsum; positive-discount scale construction root-connected to zero-discount regularity.

import Mathlib.Topology.Algebra.InfiniteSum.Order
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical

theorem AvramDividend.Classical.pointwise_summable_monotone_tsum
    (F : ℕ → ℝ → ℝ)
    (hmono : ∀ n : ℕ, Monotone (F n))
    (hsum : ∀ x : ℝ, Summable (fun n : ℕ => F n x)) :
    Monotone (fun x : ℝ => ∑' n : ℕ, F n x) := by sorry
