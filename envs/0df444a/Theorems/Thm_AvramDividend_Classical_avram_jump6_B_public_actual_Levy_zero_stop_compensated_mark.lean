-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_public_actual_Levy_zero_stop_compensated_mark
-- name    : AvramDividend.Classical.avram_jump6_B_public_actual_Levy_zero_stop_compensated_mark
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T08:04:57.187712+00:00
-- url     : https://prove2.me/theorems/ef39f40d-fcb1-4880-af63-6d09b7d850a8
-- title:
--   Actual original Levy stopped compensated jump mark vanishes at zero clock
-- statement:
--   For the original spectrally negative Levy jump measure, time-zero support is null and the physical-time source compensator has no time-zero atom. A direct proof, using only Proved public measure lemmas, proves that the actual stopped jump-minus-compensator vanishes at clock zero. No private or newly published helper is imported.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_jump_measure_zero_initial_time
import Theorems.Thm_AvramDividend_Classical_avram_bva92_original_mapped_compensator_zero_time_supported_real_integral
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_public_actual_Levy_zero_stop_compensated_mark
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (σ : Ω → ℝ≥0) (H : ℝ≥0 → Ω → ℝ → ℝ) :
    ∀ ω, σ ω = 0 →
      (∫ p, (if p.1 ≤ σ ω then H p.1 ω p.2 else 0)
        ∂((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) -
      (∫ t, (∫ z, if t ≤ σ ω then H t ω z else 0
          ∂(X.ν.restrict (Iio (0 : ℝ))))
        ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal)) = 0 := by sorry
