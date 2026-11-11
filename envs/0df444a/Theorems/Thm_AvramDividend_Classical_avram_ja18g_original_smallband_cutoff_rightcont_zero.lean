-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18g_original_smallband_cutoff_rightcont_zero
-- name    : AvramDividend.Classical.avram_ja18g_original_smallband_cutoff_rightcont_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T23:23:49.317547+00:00
-- url     : https://prove2.me/theorems/352103fe-ac4f-4d83-ad1d-68e6350087db
-- title:
--   Original process finite compensated marked cutoff paths are right-continuous and start at zero
-- statement:
--   For each original process sample path and each integer small-band cutoff, prove all-time right-continuity and zero at time zero of the compensated finite-mark jump sum. Reuse Proved e2cc7398 marked step right-continuity and Proved 1c1d4731 finite-band original source representation. This isolates original same-space path topology from the analytic locally uniform limit; no auxiliary process or filtration replacement.
-- source:
--   Sound original-process child for path-only theorem 9362895e, root-connected Avram bounded-band compensation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18g_original_smallband_cutoff_rightcont_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∀ (n : ℕ) (ω : Ω),
      (∀ t : ℝ≥0,
        ContinuousWithinAt
          (fun s : ℝ≥0 =>
            avram_p4_h_gaussian_intrinsic_small_band_compensated X n s ω)
          (Ici t) t) ∧
      avram_p4_h_gaussian_intrinsic_small_band_compensated X n 0 ω = 0 := by sorry
