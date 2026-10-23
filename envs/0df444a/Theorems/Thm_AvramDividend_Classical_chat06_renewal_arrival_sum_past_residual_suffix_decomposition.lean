-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_renewal_arrival_sum_past_residual_suffix_decomposition
-- name    : AvramDividend.Classical.chat06_renewal_arrival_sum_past_residual_suffix_decomposition
-- status  : Open
-- author  : @WillR
-- created : 2026-10-22T08:20:50.153176+00:00
-- url     : https://prove2.me/theorems/f1031340-88a4-453a-ba0b-e41fade07b90
-- title:
--   Renewal arrival sums separate into past, residual and future suffix
-- statement:
--   Every finite renewal arrival sum with a later index decomposes into the historical prefix, the next waiting time and the following finite suffix. This algebraic identity supports expressing renewal count increments as functions of the residual waiting time and the independent future waiting-time sequence.
-- source:
--   bv_arrival_sum_residual_future_decomposition_v5_chat06_20261022.lean, 14 lines, 576 bytes, SHA-256 40e62872bb5d6a7f8e5738fd38fd08327548eb70c33b41f71ae6176c7a7e49e4; private probe c953df34-1b64-4c13-a063-f27e89eb3680 reached intentional sentinel with no candidate source errors.

import Mathlib.Probability.Distributions.Exponential
import Mathlib.Tactic

open MeasureTheory Measure ProbabilityTheory Set
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.chat06_renewal_arrival_sum_past_residual_suffix_decomposition
    (τ : ℕ → ℝ) (n k : ℕ) :
    (∑ i ∈ Finset.range (n + k + 1), τ i) =
      ((∑ i ∈ Finset.range n, τ i) + τ n) +
        ∑ j ∈ Finset.range k, τ (n + 1 + j) := by sorry
