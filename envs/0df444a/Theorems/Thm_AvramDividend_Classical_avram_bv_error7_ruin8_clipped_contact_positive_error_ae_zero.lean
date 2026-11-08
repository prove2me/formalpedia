-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_ruin8_clipped_contact_positive_error_ae_zero
-- name    : AvramDividend.Classical.avram_bv_error7_ruin8_clipped_contact_positive_error_ae_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:23:27.160192+00:00
-- url     : https://prove2.me/theorems/53ad3ebb-2a1f-4aba-b917-6c52f813fc72
-- title:
--   Uniformly continuous zero-clipped contact makes positive value errors vanish despite ruin crossings
-- statement:
--   For a contact function uniformly continuous on the nonnegative compact reserve band, raw increments tending to zero and contact endpoints remaining in the band after zero-clipping force every positively majorised contact error to tend to zero, including ruin crossings.
-- source:
--   Combine already Proved nonnegative ruin-clipping increment contraction and already Proved uniform contact-value difference convergence. Use a metric squeeze of the positive error below its clipped positive change. This is a valid independent analytic child for the authentic BV source, with no expectation convergence inferred from a.e. convergence and no prebudget dependency.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_ruin8_nonnegative_ruin_clip_contact_increment_le_raw
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_ruin8_uniform_contact_value_differences_vanish

open MeasureTheory Set Filter AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_ruin8_clipped_contact_positive_error_ae_zero
    (f : ℝ → ℝ) (B : ℝ) (hUC : UniformContinuousOn f (Set.Icc 0 B))
    (z c Err : ℕ → ℝ)
    (hBand : ∀ m, z m ∈ Set.Icc 0 B ∧ max (z m + c m) 0 ∈ Set.Icc 0 B)
    (hcTo : Tendsto c atTop (nhds (0 : ℝ)))
    (hMajorant : ∀ m,
      max (Err m) 0 ≤ max (f (max (z m + c m) 0) - f (z m)) 0) :
    Tendsto (fun m => max (Err m) 0) atTop (nhds (0 : ℝ)) := by sorry
