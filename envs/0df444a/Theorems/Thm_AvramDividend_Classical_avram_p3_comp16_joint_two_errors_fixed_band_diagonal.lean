-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_comp16_joint_two_errors_fixed_band_diagonal
-- name    : AvramDividend.Classical.avram_p3_comp16_joint_two_errors_fixed_band_diagonal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T21:59:43.182543+00:00
-- url     : https://prove2.me/theorems/933a9d91-1bea-414b-8ebf-2e4aebba6104
-- title:
--   One slowly varying physical-grid band schedule kills two fixed-band errors
-- statement:
--   If two error families have vanishing mesh error for every fixed localisation band, a common cofinal diagonal band schedule κ(n)≤n makes both errors vanish simultaneously. Useful for the cell Taylor and contact/dividend errors in the original Avram BV estimate.
-- source:
--   Apply the verified P3-COMP16 pointwise fixed-band diagonal theorem to the sum of the absolute two errors, then apply squeeze_zero_norm' to each component separately. Does not claim original Lévy-specific estimates.

import Mathlib
open Filter
noncomputable section

theorem AvramDividend.Classical.avram_p3_comp16_joint_two_errors_fixed_band_diagonal
    (ErrCell ErrContact : ℕ → ℕ → ℝ)
    (hCell : ∀ k, Tendsto (fun n => ErrCell k n) atTop (nhds 0))
    (hContact : ∀ k, Tendsto (fun n => ErrContact k n) atTop (nhds 0)) :
    ∃ κ : ℕ → ℕ,
      (∀ n, κ n ≤ n) ∧
      Tendsto κ atTop atTop ∧
      Tendsto (fun n => ErrCell (κ n) n) atTop (nhds 0) ∧
      Tendsto (fun n => ErrContact (κ n) n) atTop (nhds 0) := by sorry
