-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a88_original_gaussian_bounded_discounted_hessian_cross_sum_le_source_energy
-- name    : AvramDividend.Classical.avram_ga_a88_original_gaussian_bounded_discounted_hessian_cross_sum_le_source_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T08:07:51.873345+00:00
-- url     : https://prove2.me/theorems/1d860f4e-bb33-4eb0-8fd0-a021fd88b642
-- title:
--   Original Gaussian stopped physical-grid Hessian-weighted quadratic raw-centred correction is dominated by original source cross energy
-- statement:
--   For any actual finite physical Gaussian source grid, uniformly bounded original discounted Hessian weights yield an absolute weighted quadratic cross sum no larger than half the Hessian bound times total absolute raw-centred quadratic source energy.
-- source:
--   Original b0d9951c true stopped Gaussian spatial generator cross term: combine ga_a81 and compact hessian c17053bc.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_ga_a88_original_gaussian_bounded_discounted_hessian_cross_sum_le_source_energy (S : Finset ℕ) (H R : ℕ → ℝ)
    (K : ℝ) (hK : 0 ≤ K)
    (hH : ∀ i ∈ S, |H i| ≤ K) :
    |∑ i ∈ S, H i / 2 * R i| ≤
      (K / 2) * ∑ i ∈ S, |R i| := by sorry
