-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_annulus14_original_shifted_fullcutoff_factorial_exact
-- name    : AvramDividend.Classical.avram_mix_annulus14_original_shifted_fullcutoff_factorial_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T09:16:43.631005+00:00
-- url     : https://prove2.me/theorems/cb91be32-0bde-4ce5-abc1-eabb9ecf0b14
-- title:
--   Shifted physical full-cutoff factorial second moment has exact squared Levy rate
-- statement:
--   The full-cutoff original-process jump count in any physical half-open time interval has an integrable real factorial count with expectation equal to the squared interval rate. It transfers the already-Proved zero-origin exact moment via original stationary increments, respecting interval endpoints.
-- source:
--   Proved 0a13392f exact origin factorial, 34cdb144 stationary interval moments. Necessary full-cutoff same-cell diagonal of d924a79e and 6ea0212e.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f2_original_band_count_factorial_moment_exact
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_intrinsic_marked_real_moment_stationary
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_annulus14_original_shifted_fullcutoff_factorial_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s T : ℝ≥0) (m : ℕ) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s (s + T) ×ˢ Iic (-(1 / ((m : ℝ) + 1))))
    let r : ℝ := ((T : ℝ≥0∞) *
      X.ν (Iic (-(1 / ((m : ℝ) + 1))))).toReal
    Integrable (fun ω => (N ω).toReal * ((N ω).toReal - 1)) P ∧
      (∫ ω, (N ω).toReal * ((N ω).toReal - 1) ∂P) = r ^ 2 := by sorry
