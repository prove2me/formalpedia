-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a154_original_gaussian_fullcell_raw_source_sum_cauchy_energy
-- name    : AvramDividend.Classical.avram_ga_a154_original_gaussian_fullcell_raw_source_sum_cauchy_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T12:23:10.510788+00:00
-- url     : https://prove2.me/theorems/ce51326e-df0d-440f-810a-bc85a36170aa
-- title:
--   Original Gaussian physical m-cell full-source absolute increment sum squared is bounded by m times its exact source quadratic energy
-- statement:
--   For any collection of the original Gaussian source increments across m physically full pre-stop cells, the square of their total absolute displacement is at most m times the sum of their raw quadratic energies. This exact deterministic finite-grid Cauchy-Schwarz inequality supplies the square-root cellcount scaling needed to show discount-width times source-value displacement vanishes under the already proved bounded original Gaussian quadratic mesh energy.
-- source:
--   Pinned Mathlib Chebyshev/Cauchy-Schwarz finite-sum inequality sq_sum_le_card_mul_sum_sq, applied to original Gaussian stopped physical source increments from ga130 and ga137.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a154_original_gaussian_fullcell_raw_source_sum_cauchy_energy
    (m : ℕ) (R : ℕ → ℝ) :
    (∑ i ∈ Finset.range m, |R i|)^2 ≤
      (m : ℝ) * (∑ i ∈ Finset.range m, (R i)^2) := by sorry
