-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat08_eventually_zero_finite_ennreal_weights_tsum_lt_top
-- name    : AvramDividend.Classical.chat08_eventually_zero_finite_ennreal_weights_tsum_lt_top
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T23:41:44.362616+00:00
-- url     : https://prove2.me/theorems/32b4b4bb-9dd6-4feb-b6e9-66acd999eecc
-- title:
--   An eventually-zero sequence of finite ENNReal payments has finite total reward
-- statement:
--   If extended nonnegative payments are finite term by term and vanish beyond a random finite index, their countable sum is strictly below infinity. This is the finite-ruin reward summability bridge for killed first-record payments.
-- source:
--   Mathlib.Topology.Algebra.InfiniteSum.Basic and Mathlib.Data.ENNReal.BigOperators.

import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat08_eventually_zero_finite_ennreal_weights_tsum_lt_top
    (w : ℕ → ℝ≥0∞)
    (hfinite : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → w n = 0)
    (hterms : ∀ n, w n < ⊤) :
    (∑' n : ℕ, w n) < ⊤ := by sorry
