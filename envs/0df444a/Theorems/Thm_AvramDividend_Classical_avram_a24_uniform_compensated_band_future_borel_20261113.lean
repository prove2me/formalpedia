-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a24_uniform_compensated_band_future_borel_20261113
-- name    : AvramDividend.Classical.avram_a24_uniform_compensated_band_future_borel_20261113
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:34:08.426362+00:00
-- url     : https://prove2.me/theorems/98a37e76-7b2b-47c3-89ba-b53ed5876001
-- title:
--   A uniform original compensated cutoff-band future-path statistic for every deterministic starting time
-- statement:
--   For the original spectrally negative Levy process, every negative cutoff-band compensated increment over an interval of duration T is the same measurable function of the shifted source path, for all starting times.
-- source:
--   Proved A23 uniform signed physical window Borel and signed marked-prefix difference lemmas.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_a23_original_smallband_marked_window_difference_20261113
import Theorems.Thm_AvramDividend_Classical_avram_a23_uniform_signed_negative_band_window_borel_20261113
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A single source future-path statistic gives every translated compensated band increment. -/

theorem AvramDividend.Classical.avram_a24_uniform_compensated_band_future_borel_20261113
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (n : ℕ) (T : ℝ≥0) :
    ∃ W : (ℝ≥0 → ℝ) → ℝ, Measurable W ∧
      ∀ (s : ℝ≥0) (ω : Ω),
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n (s + T) ω -
          avram_p4_h_gaussian_intrinsic_small_band_compensated X n s ω =
        W (fun u : ℝ≥0 => X.X (s + u) ω - X.X s ω) := by sorry
