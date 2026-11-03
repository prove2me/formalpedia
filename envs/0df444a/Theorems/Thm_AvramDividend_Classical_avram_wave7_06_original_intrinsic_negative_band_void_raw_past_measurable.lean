-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_intrinsic_negative_band_void_raw_past_measurable
-- name    : AvramDividend.Classical.avram_wave7_06_original_intrinsic_negative_band_void_raw_past_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T23:59:16.959471+00:00
-- url     : https://prove2.me/theorems/0b2a8d21-7bab-4123-89a6-4755d507a75f
-- title:
--   Actual original-process negative-band void event belongs to the raw past filtration
-- statement:
--   For the original spectrally negative Lévy process and its raw filtration, the event that the intrinsic marked-counting measure records no jumps in (0,T] with size at most −1/(n+1) is measurable at time T, without postulating a predictable representation or switching probability spaces. It is discharged by exact frozen-prefix count representation and source adaptedness.
-- source:
--   W7-06 original-filtration small-jump compensated martingale, raw past-void step for stopped semigroup.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_intrinsic_negative_band_void_raw_past_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ) :
    MeasurableSet[𝓕 T] {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0} := by sorry
