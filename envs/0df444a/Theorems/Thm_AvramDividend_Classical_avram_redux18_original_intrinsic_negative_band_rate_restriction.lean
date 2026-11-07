-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_redux18_original_intrinsic_negative_band_rate_restriction
-- name    : AvramDividend.Classical.avram_redux18_original_intrinsic_negative_band_rate_restriction
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T18:14:12.460204+00:00
-- url     : https://prove2.me/theorems/23b0f36b-71c0-4f0a-b260-48671ff89c05
-- title:
--   Original intrinsic negative-band mark rate agrees with the Levy measure
-- statement:
--   For any positive physical horizon, the original spectrally negative Levy process's intrinsic marked jump-rate measure is exactly its Levy measure on every negative Borel band separated from zero, provided its intrinsic mark-rate characterisation holds on the band. This directly combines the already Proved intrinsic jump-count intensity characterisation with the original negative Borel Levy rate theorem.
-- source:
--   Compare the two Proved original-process count-intensity identities on arbitrary measurable subsets of Iic(-epsilon), cancel the nonzero finite time factor with ENNReal.mul_left_inj, and extend restricted measures. The original X and original probability measure P remain unchanged.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_zero_origin_separated_negative_borel_levy_rate
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_redux18_original_intrinsic_negative_band_rate_restriction
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (hT : 0 < T)
    (ε : ℝ) (hε : 0 < ε) (markRate : Measure ℝ)
    (hMark : ∀ C : Set ℝ, MeasurableSet C → C ⊆ Iic (-ε) →
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ C) ∂P) = (T : ℝ≥0∞) * markRate C) :
    markRate.restrict (Iic (-ε)) = X.ν.restrict (Iic (-ε)) := by sorry
