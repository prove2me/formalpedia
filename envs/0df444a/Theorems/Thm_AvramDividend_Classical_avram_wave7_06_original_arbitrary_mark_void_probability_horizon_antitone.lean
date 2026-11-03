-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_arbitrary_mark_void_probability_horizon_antitone
-- name    : AvramDividend.Classical.avram_wave7_06_original_arbitrary_mark_void_probability_horizon_antitone
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T15:25:07.98719+00:00
-- url     : https://prove2.me/theorems/3f1dc5e3-1c59-4426-8e02-066c85215339
-- title:
--   Any original marked no-jump event decreases in probability with time
-- statement:
--   For the genuine X.X intrinsic jump counting measure and any mark set B, the P mass of the no-B-mark event over (0,T] cannot increase when T increases. This source event inclusion and measure monotonicity requires no independence or auxiliary Poisson law.
-- source:
--   Source-faithful general mark-event bridge supporting future marked-grid original compensation proof; generalises previous cutoff-specific horizon void antitonicity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_arbitrary_mark_void_probability_horizon_antitone
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S T : ℝ≥0) (B : Set ℝ) (hST : S ≤ T) :
    (let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
     P {ω : Ω | NX ω (Ioc 0 T ×ˢ B) = 0} ≤
     P {ω : Ω | NX ω (Ioc 0 S ×ˢ B) = 0}) := by sorry
