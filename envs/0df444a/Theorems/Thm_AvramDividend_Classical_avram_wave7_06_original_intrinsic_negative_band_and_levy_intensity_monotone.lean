-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_intrinsic_negative_band_and_levy_intensity_monotone
-- name    : AvramDividend.Classical.avram_wave7_06_original_intrinsic_negative_band_and_levy_intensity_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:29:34.918831+00:00
-- url     : https://prove2.me/theorems/3b526dac-e40d-49e9-a571-d1130411adbd
-- title:
--   Original intrinsic negative-band count and Lévy intensity are monotone in the truncation index
-- statement:
--   For n≤m, the actual intrinsic marked-jump count in (0,T] with negative marks at or below -1/(n+1) is at most the same count for -1/(m+1); the genuine Lévy intensity ν of those bands obeys the same inequality. This establishes the exact increasing truncation order for both source and compensator.
-- source:
--   Source-faithful negative-band truncation order for the original L²/L¹ small-jump compensator and martingale programme, mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_intrinsic_negative_band_and_levy_intensity_monotone
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (T : ℝ≥0) (n m : ℕ) (hnm : n ≤ m) :
    (let NX : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
     NX (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) ≤
       NX (Ioc 0 T ×ˢ Iic (-(1 / ((m : ℝ) + 1)))) ∧
     X.ν (Iic (-(1 / ((n : ℝ) + 1)))) ≤
       X.ν (Iic (-(1 / ((m : ℝ) + 1)))) ) := by sorry
