-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_negative_compact_mean_measure_lintegral
-- name    : AvramDividend.Classical.avram_p2_e_compensator_original_negative_compact_mean_measure_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T09:01:23.420085+00:00
-- url     : https://prove2.me/theorems/fcb4ca7f-140a-4a4c-8059-32b2a6f802e5
-- title:
--   Original expected marked-jump measure agrees with Levy integral on nonnegative compact negative tests
-- statement:
--   For the actual spectrally negative Levy process and an expected original unit-time intrinsic mark measure rho, the nonnegative integral of every nonnegative compactly supported continuous test strictly below zero agrees with the original Levy integral. This is the finite-support Tonelli and source finite-jump bridge to the unsolved compact-test uniqueness step. No compensator or source rate is assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_e_compensator_original_negative_compact_mean_measure_lintegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (ρ : Measure ℝ)
    (hρ : ∀ B : Set ℝ, MeasurableSet B →
      ρ B = (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (1 : ℝ≥0) ×ˢ B) ∂P))
    (g : ℝ → ℝ) (hg : Continuous g)
    (hc : IsCompact (tsupport g))
    (hneg : tsupport g ⊆ Iio (0 : ℝ))
    (hgnonneg : ∀ y : ℝ, 0 ≤ g y) :
    (∫⁻ y, ENNReal.ofReal (g y) ∂ρ) =
      ENNReal.ofReal (∫ y : ℝ, g y ∂(X.ν.restrict (Iio (0 : ℝ)))) := by sorry
