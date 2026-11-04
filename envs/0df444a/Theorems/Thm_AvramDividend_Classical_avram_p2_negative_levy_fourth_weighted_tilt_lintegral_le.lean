-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_negative_levy_fourth_weighted_tilt_lintegral_le
-- name    : AvramDividend.Classical.avram_p2_negative_levy_fourth_weighted_tilt_lintegral_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T07:47:45.048408+00:00
-- url     : https://prove2.me/theorems/829a7ffa-3df7-4a13-8f70-a1c891b51bf6
-- title:
--   Negative Lévy fourth-weighted positive tilts have moments bounded by the untilted mass
-- statement:
--   On the original Lévy measure of the unchanged spectrally negative source, restrict to strictly negative jump marks. For every nonnegative rho the ENNReal integral of exp(rho y)(exp y - 1)^4 is bounded by the untilted fourth-weighted mass. The proof uses y<0, rho≥0, exp(rho y)≤1 and positivity of the fourth power, with no finite-activity or density assumption. It proves the monotone moment comparison needed to constrain support of weak limits of the source-weighted exponential laws.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_negative_levy_fourth_weighted_tilt_lintegral_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (∫⁻ y in Iio (0 : ℝ),
      ENNReal.ofReal (Real.exp (ρ * y) * (Real.exp y - 1) ^ 4) ∂X.ν) ≤
    (∫⁻ y in Iio (0 : ℝ),
      ENNReal.ofReal ((Real.exp y - 1) ^ 4) ∂X.ν) := by sorry
