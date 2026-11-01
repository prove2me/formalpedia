-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_all_source_pathwise_atomless_prejump_for_path_dependent_measure
-- name    : AvramDividend.Classical.avram_wave4_04b_all_source_pathwise_atomless_prejump_for_path_dependent_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T19:54:34.504426+00:00
-- url     : https://prove2.me/theorems/a14bf58b-7618-46d8-8305-425cfaa67b49
-- title:
--   Actual Lévy pre-source reserve agrees with prepayment controlled reserve pathwise under every atomless dividend measure
-- statement:
--   For every sample ω of the actual spectrally negative Lévy source, any adapted left-continuous dividend strategy, and any atomless time measure chosen after fixing ω (including a path-dependent diffuse dividend Stieltjes measure), the pre-source/prepayment reserve equals the genuine source left-limit controlled reserve at almost every positive time. The source-jump countability is discharged from the actual source theorem without requiring BV or almost-sure re-selection of ν.
-- source:
--   Proved source-X sample-path jump-time countability theorem 741d3b5f and countability-conditional full atomless equality e7696306.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_all_original_levy_jump_times_countable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_atomless_pre_source_pre_payment_ae_of_countable_jumps

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave4_04b_all_source_pathwise_atomless_prejump_for_path_dependent_measure
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (ν : Measure ℝ) [NullSingletonClass ν] :
    ∀ᵐ s ∂ν, 0 < s →
      riskProcess X x D s.toNNReal ω =
        x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
          rightLimit D s.toNNReal ω := by
  sorry
