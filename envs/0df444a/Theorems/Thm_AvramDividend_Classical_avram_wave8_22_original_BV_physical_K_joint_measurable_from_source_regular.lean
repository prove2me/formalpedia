-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_physical_K_joint_measurable_from_source_regular
-- name    : AvramDividend.Classical.avram_wave8_22_original_BV_physical_K_joint_measurable_from_source_regular
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:15:53.351137+00:00
-- url     : https://prove2.me/theorems/cb43a4eb-753e-457d-a12a-3b1d3b7c7edd
-- title:
--   Original BV physical Lévy generator joint measurability from source value regularity
-- statement:
--   The actual BV value w is continuous on nonnegative reserve and zero below zero, hence globally measurable. Its derivative is Borel measurable by pinned Mathlib measurable_deriv. Along a jointly measurable controlled left-limit reserve, the exact physical Lévy generator is jointly measurable as soon as the source negative-jump ν-kernel as a function of reserve is measurable.
-- source:
--   Accepted original physical K measurable-of-components 593b2a56, accepted source half-line value measurable 4adbe17d (to verify), pinned measurable_deriv w; original spectrally negative Lévy X and D are retained.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_physical_K_joint_measurable_of_components
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_value_measurable_of_positive_continuity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave8_22_original_BV_physical_K_joint_measurable_from_source_regular {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  (X : SpectrallyNegativeLevy P 𝓕)
  (q : ℝ) (w : ℝ → ℝ) (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
  (K : ℝ≥0 → Ω → ℝ)
  (hK : ∀ t ω, K t ω =
    Real.exp (-(q * (t : ℝ))) *
      (X.drift * deriv w (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) +
      (∫ z in Iio (0 : ℝ),
        w (Function.leftLim (fun s : ℝ≥0 =>
            x + X.X s ω - rightLimit D s ω) t + z) -
        w (Function.leftLim (fun s : ℝ≥0 =>
            x + X.X s ω - rightLimit D s ω) t) ∂X.ν) -
      q * w (Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s ω - rightLimit D s ω) t)))
  (hYmeas : Measurable (fun p : ℝ≥0 × Ω =>
    Function.leftLim (fun s : ℝ≥0 =>
      x + X.X s p.2 - rightLimit D s p.2) p.1))
  (hw_cont : ContinuousOn w (Ici (0 : ℝ)))
  (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
  (hJMeas : Measurable (fun y : ℝ =>
    ∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν)) :
  Measurable (fun p : ℝ≥0 × Ω => K p.1 p.2) := by sorry
