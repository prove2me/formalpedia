-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_twoagentA_public_original_physical_finite_band_signed_integral_partition_20261122
-- name    : AvramDividend.Classical.avram_twoagentA_public_original_physical_finite_band_signed_integral_partition_20261122
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T14:12:12.379841+00:00
-- url     : https://prove2.me/theorems/136b067c-70d1-4e13-ab7b-f8d23794f96f
-- title:
--   Actual original physical finite negative mark source d89854b4
-- statement:
--   Reuse already accepted original same-X finite negative physical marked-jump integral proof, with all private original mark and annulus lemmas replaced by the identical publicly proven shared declarations. Source is genuinely original signed mark; no finite total ν hypothesis.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_public_original_marked_interval_integral_adjacent_additivity_20261122
open MeasureTheory Set AvramDividend.Classical
open scoped Classical NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_twoagentA_public_original_physical_finite_band_signed_integral_partition_20261122
    (μ : Measure (ℝ≥0 × ℝ)) (T : ℝ≥0) (n m : ℕ)
    (hnm : n ≤ m)
    (hInt : IntegrableOn (fun p : ℝ≥0 × ℝ => p.2)
      (Ioc (0 : ℝ≥0) T ×ˢ
        Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))) μ) :
    (∫ p in Ioc (0 : ℝ≥0) T ×ˢ
      Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1))), p.2 ∂μ) =
    ∑ i ∈ Finset.Ico n m,
      ∫ p in Ioc (0 : ℝ≥0) T ×ˢ
        Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((i : ℝ) + 2))), p.2 ∂μ := by sorry
