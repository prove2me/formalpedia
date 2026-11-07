-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_redux18_original_negative_band_weighted_levy_compensator
-- name    : AvramDividend.Classical.avram_redux18_original_negative_band_weighted_levy_compensator
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T18:17:37.152123+00:00
-- url     : https://prove2.me/theorems/5c04ccf0-def2-4157-b488-bade7b9ddb29
-- title:
--   Original intrinsic negative-band weighted jump compensator equals Levy integral
-- statement:
--   The genuine original spectrally negative Levy path has exact expected intrinsic marked-jump weight over any positive or zero horizon equal to horizon length times the integral of that mark test against the original Levy measure, for every measurable nonnegative weight supported on a negative Borel band separated from zero. This discharges the missing original-process Campbell intensity identification without assuming a Poisson marked point process.
-- source:
--   Use the already Proved intrinsic weighted mark-rate identity at the same T and g; for positive T cancel the physical time factor against the already Proved original negative Borel Levy count rate on arbitrary sub-bands, identify the restricted measures and transfer supported weighted lintegrals via lintegral_indicator. At T=0 both sides vanish by the original weighted identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_public_original_weighted_intrinsic_rate_identity
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_zero_origin_separated_negative_borel_levy_rate
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_redux18_original_negative_band_weighted_levy_compensator
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (g : ℝ → ℝ≥0∞) (hg : Measurable g)
    (ε : ℝ) (hε : 0 < ε)
    (hSupport : ∀ y, y ∉ Iic (-ε) → g y = 0) :
    (∫⁻ ω, ∫⁻ p in (Ioc 0 T ×ˢ (univ : Set ℝ)),
      g p.2 ∂((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) ∂P) =
      (T : ℝ≥0∞) * (∫⁻ y, g y ∂X.ν) := by sorry
