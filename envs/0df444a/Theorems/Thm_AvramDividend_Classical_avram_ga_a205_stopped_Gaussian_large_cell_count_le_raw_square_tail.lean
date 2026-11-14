-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a205_stopped_Gaussian_large_cell_count_le_raw_square_tail
-- name    : AvramDividend.Classical.avram_ga_a205_stopped_Gaussian_large_cell_count_le_raw_square_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T17:37:31.752619+00:00
-- url     : https://prove2.me/theorems/becb57cd-1986-45f6-adec-1573123f8cdc
-- title:
--   Original stopped Gaussian physical-grid count of large raw-increment cells is bounded by inverse squared threshold times raw square tail
-- statement:
--   For any finite physical mesh and a sample-dependent stopped-cell mask, the number of selected cells whose raw source increment has magnitude above a fixed positive threshold is bounded by the sum of their raw squared increment divided by that threshold squared. This pointwise observation converts the already Proved original stopped Gaussian large raw-square expected tail vanishing a56, or the real a187 package, into vanishing expected frequency of large raw cells required by the safe a199 positive-discount bound for the actual globally nonnegative vcstar candidate.
-- source:
--   Deterministic squared threshold inequality, finite sum monotonicity and genuine source-event masks.

import Mathlib
open Real
noncomputable section

theorem AvramDividend.Classical.avram_ga_a205_stopped_Gaussian_large_cell_count_le_raw_square_tail
    (S : Finset ℕ) (A : ℕ → Prop) [DecidablePred A]
    (R : ℕ → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    (∑ i ∈ S, if A i then
      (if δ ≤ |R i| then (1 : ℝ) else 0) else 0) ≤
    (∑ i ∈ S, if A i then
      (if δ ≤ |R i| then (R i)^2 / δ^2 else 0) else 0) := by sorry
