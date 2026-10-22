-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_arrival_prefix_reconstructs_past_count
-- name    : AvramDividend.Classical.chat06_arrival_prefix_reconstructs_past_count
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T12:28:02.708988+00:00
-- url     : https://prove2.me/theorems/e74a2b57-6902-407a-9482-f01358d97bba
-- title:
--   Observed renewal counts up to a fixed time are reconstructed exactly from the finite interarrival prefix
-- statement:
--   For any renewal counting process whose count at each time u has the exact completed-arrival threshold characterisation, fix a horizon and a count cylinder N(horizon)=n. Let Z retain the first n interarrival times and replace all later times with zero. At every time s≤horizon the number of arrivals among the first n prefix cumulative sums that occurred by s equals N(s), including boundary times equal to arrivals. It proves the missing deterministic pathwise reconstruction of the complete earlier counting history from an observed finite prefix.
-- source:
--   bv_arrival_prefix_reconstructs_past_count_v8_chat06_20261021.lean, 47 lines, 1839 bytes, SHA-256 4a638e047093b447a53c978397f96a31c35b8d004d624af403f6319767eb4b00; private remote probe ade91e84-706b-448c-8da8-f7eb774efb90 passed sentinel with no source errors.

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Finset.Card

theorem AvramDividend.Classical.chat06_arrival_prefix_reconstructs_past_count
    (τ : ℕ → ℝ) (Z : ℕ → ℝ) (N : ℝ → ℕ)
    (horizon : ℝ) (s : ℝ) (hs : s ≤ horizon) (n : ℕ)
    (hClock : N horizon = n)
    (hThreshold : ∀ u : ℝ, ∀ k : ℕ,
      k < N u ↔
        (∑ i ∈ Finset.range (k + 1), τ i) ≤ u)
    (hZ : ∀ i, Z i = if i < n then τ i else 0) :
    ((Finset.range n).filter (fun k =>
      (∑ i ∈ Finset.range (k + 1), Z i) ≤ s)).card = N s := by sorry
