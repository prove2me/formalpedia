-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_fin14_original_bounded_clock_negative_jump_count_L1_rate
-- name    : AvramDividend.Classical.avram_mix_fin14_original_bounded_clock_negative_jump_count_L1_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T11:33:35.981952+00:00
-- url     : https://prove2.me/theorems/dfcb3913-73a0-48e0-9faf-e585fe7d12ed
-- title:
--   Original finite-activity bounded random-clock negative jump count has finite expectation
-- statement:
--   For an original spectrally negative Levy process with finite negative jump intensity, and any arbitrary random clock bounded by an integer horizon, prove the literal original negative marked jump count before that clock has finite expectation. Use the original all-Borel marked unconditional Levy rate for the integer ceiling and the pointwise inclusion of time windows; integrate by lintegral_mono. No stopping-time-measurability, bounded-variation, or auxiliary process assumption is introduced. Supplies a source-exact L1 jump count domination for the ruin-clipped finite mixed Ito-Meyer compensation budget.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_borel_marked_unconditional_levy_rate
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_fin14_original_bounded_clock_negative_jump_count_L1_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (σ : Ω → ℝ≥0)
    (hBound : ∀ ω, σ ω ≤ (n : ℝ≥0)) :
    (∫⁻ ω,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (σ ω) ×ˢ Iio (0 : ℝ)) ∂P) < ⊤ := by sorry
