-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18_original_cutoff_gaussian_square_L1
-- name    : AvramDividend.Classical.avram_ja18_original_cutoff_gaussian_square_L1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-10T20:52:17.320031+00:00
-- url     : https://prove2.me/theorems/e8635d59-e83c-4198-897b-7861ff9390bf
-- title:
--   Original finite-cutoff intrinsic Gaussian residual square integrable at every time
-- statement:
--   Under Standing and finite negative jump intensity, the square of the original physical intrinsic Gaussian residual at every finite cutoff and deterministic time is integrable. Large jump cancellation is essential; no second moment of the original full state is asserted.
-- source:
--   Exact first conjunct of 74450e6a. Potential approach: prove stochastic square integrability of original X minus actual large jump sum by the source Lévy-Itô variance formula. Existing Proved original bounded small-band L2 isometry and finite-source identities apply without auxiliary process replacement.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18_original_cutoff_gaussian_square_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (n : ℕ) (t : ℝ≥0), Integrable
      (fun ω => (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω) ^ 2) P := by sorry
