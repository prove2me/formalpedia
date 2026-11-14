-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB310_translated_inverse_sqrt_cell_integrable
-- name    : AvramDividend.Classical.avram_gbB310_translated_inverse_sqrt_cell_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T00:07:07.516344+00:00
-- url     : https://prove2.me/theorems/824bafce-e04f-4609-bcb3-130d2c866607
-- title:
--   Inverse-square-root Gaussian elapsed-time kernel is integrable on every finite translated physical cell
-- statement:
--   For a real physical-cell start and nonnegative width, the inverse-square-root elapsed-time singular kernel is integrable on the right-closed cell. Apply the pinned theorem intervalIntegral.intervalIntegrable_rpow' for exponent minus one half, translate the physical cell, and use intervalIntegrable_iff_integrableOn_Ioc_of_le. This is the exact integrability input to the Proved B309 open-cell nonnegative Lebesgue integral bound and the original source B308 analytic Gaussian fibre estimate.

import Mathlib
open MeasureTheory Set
noncomputable section

theorem AvramDividend.Classical.avram_gbB310_translated_inverse_sqrt_cell_integrable (s δ : ℝ) (hδ : 0 ≤ δ) :
    IntegrableOn (fun t : ℝ => (t - s) ^ (-(1 / 2 : ℝ)))
      (Set.Ioc s (s + δ)) volume := by sorry
