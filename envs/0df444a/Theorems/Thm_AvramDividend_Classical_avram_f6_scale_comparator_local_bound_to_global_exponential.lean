-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_scale_comparator_local_bound_to_global_exponential
-- name    : AvramDividend.Classical.avram_f6_scale_comparator_local_bound_to_global_exponential
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T20:58:33.42534+00:00
-- url     : https://prove2.me/theorems/8a32ffef-5d02-40dd-a48d-c247aaf7dce8
-- title:
--   Original topcap HJB scale-function comparison and compact local bound imply global exponential growth
-- statement:
--   If authentic candidate w is bounded above near zero, its genuine q-scale W obeys exponential growth, and the first-exit comparison w≤A W holds on y≥1, then w≤K exp(θ y) globally on y≥0. Pure scalar proof using nonnegative constants and max, no synthetic stopping times.

import Mathlib
set_option autoImplicit false
open MeasureTheory Set Topology
noncomputable section

theorem AvramDividend.Classical.avram_f6_scale_comparator_local_bound_to_global_exponential
    (w W : ℝ → ℝ) (θ A K0 K1 : ℝ)
    (hθ : 0 ≤ θ) (hA : 0 ≤ A)
    (hK0 : 0 ≤ K0) (hK1 : 0 ≤ K1)
    (hwLocal : ∀ y : ℝ, 0 ≤ y → y ≤ 1 → w y ≤ K0)
    (hScale : ∀ y : ℝ, W y ≤ K1 * Real.exp (θ * y))
    (hComp : ∀ y : ℝ, 1 ≤ y → w y ≤ A * W y) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ y : ℝ, 0 ≤ y → w y ≤ K * Real.exp (θ * y) := by sorry
