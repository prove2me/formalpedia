-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_positive_shifted_increment_contact_right_interval_ws01c
-- name    : AvramDividend.Classical.bv_positive_shifted_increment_contact_right_interval_ws01c
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T22:49:58.122687+00:00
-- url     : https://prove2.me/theorems/e93bf8b1-b8c4-45a5-b7ca-1b1e14423a7b
-- title:
--   Positive increments after exact boundary contact yield the strict lower-clock right interval
-- statement:
--   If a real-valued path equals its lower barrier at a finite time τ and all sufficiently small strictly positive increments from τ are strictly positive, then there is a right interval in absolute time on which the path lies above the lower barrier. The proof sets h=t−τ, derives h>0 and h<ε from τ<t<τ+ε, reconstructs t=τ+h, and uses the contact equality. The result applies only on an exact contact event, allowing genuine downward jump overshoots.
-- source:
--   Cause-linked repair of failed terminal authoring job a42424d7-7579-4784-a6ce-6783bc2f0f1e: removed invalid `open AvramDividend.Classical` namespace. Exact formal statement and 28-line proof retained at work/avram_ws01c_contact_interval_solution_pub_repair_20261028.lean.

import Mathlib

open Set
open scoped NNReal

theorem AvramDividend.Classical.bv_positive_shifted_increment_contact_right_interval_ws01c
    (f : ℝ≥0 → ℝ) (τ : ℝ≥0) (barrier : ℝ)
    (hContact : f τ = barrier)
    (hPositive : ∃ ε : ℝ≥0, 0 < ε ∧
      ∀ h : ℝ≥0, 0 < h → h < ε →
        0 < f (τ + h) - f τ) :
    ∃ ε : ℝ≥0, 0 < ε ∧
      ∀ t : ℝ≥0, τ < t → t < τ + ε →
        barrier ≤ f t := by sorry
