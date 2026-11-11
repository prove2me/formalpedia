-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_fin20_original_true_upper_exit_spatial_cofinality
-- name    : AvramDividend.Classical.avram_mix_fin20_original_true_upper_exit_spatial_cofinality
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T08:36:33.631947+00:00
-- url     : https://prove2.me/theorems/c4f52f64-ae7f-46fe-b910-7daf34db12e8
-- title:
--   True original spectrally negative Levy upper passage clock thresholds monotonically exhaust every finite horizon
-- statement:
--   For the original sample path of the spectrally negative Levy process, its strict upward passage clocks through levels k+1 are monotone and have extended-time supremum top. This supplies the genuine spatial upper-exit localisation S required by the original finite mixed stopped Ito/Fatou reduction, with no artificial deterministic clock and no auxiliary process. Derive using proved monotone upper-passage threshold and finite-horizon upcrossing record grid cofinality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_mono_threshold
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_record_grid_clocks_eventually_ge_horizon
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_fin20_original_true_upper_exit_spatial_cofinality
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) :
    Monotone (fun k : ℕ =>
      twoSidedExitUpTime X ((k : ℝ) + 1) ω) ∧
    (⨆ k : ℕ, twoSidedExitUpTime X ((k : ℝ) + 1) ω) = ⊤ := by sorry
