-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed12_original_finite_activity_uniform_smalljump_cutoff_ae
-- name    : AvramDividend.Classical.avram_ubv_mixed12_original_finite_activity_uniform_smalljump_cutoff_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T20:20:01.876289+00:00
-- url     : https://prove2.me/theorems/035c1c05-deb7-4fd3-851d-969cf17581f8
-- title:
--   Actual finite-activity small jumps eventually vanish uniformly on every bounded original clock
-- statement:
--   For the original finite-activity spectrally negative Levy process, almost every path has, at each bounded horizon, a natural reciprocal small-jump cutoff beyond which no nonzero original jump at any positive time up to that horizon lies in the small band. This is a simultaneous stopped path property and is suitable for identifying the actual small-jump term of the original compensated Ito-Meyer source.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed12_original_finite_activity_uniform_jump_gap_ae
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_mixed12_original_finite_activity_uniform_smalljump_cutoff_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ u : ℝ≥0, 0 < u → u ≤ T →
        |X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u| ≤
          1 / ((n : ℝ) + 1) →
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0 := by sorry
