-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_physical_K_joint_measurable_of_components
-- name    : AvramDividend.Classical.avram_wave8_22_original_BV_physical_K_joint_measurable_of_components
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:59:29.542295+00:00
-- url     : https://prove2.me/theorems/593b2a56-f619-486f-8c7b-63ac3f180103
-- title:
--   Joint measurability of original BV physical Lévy generator along controlled left-limit reserve
-- statement:
--   For the actual original spectrally negative Lévy process and dividend control, the true time-discounted physical BV drift, negative-jump ν-integral and killing term K is jointly measurable whenever the controlled left-limit reserve Y, w, its first derivative and the true ν-integral as a function of reserve are Borel measurable.
-- source:
--   Original X.drift, X.ν and controlled reserve expression, pinned Mathlib measurable_coe_nnreal_real, composition and measurable arithmetic.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave8_22_original_BV_physical_K_joint_measurable_of_components {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
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
  (hDerivMeas : Measurable (deriv w))
  (hWMeas : Measurable w)
  (hJMeas : Measurable (fun y : ℝ =>
    ∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν)) :
  Measurable (fun p : ℝ≥0 × Ω => K p.1 p.2) := by sorry
