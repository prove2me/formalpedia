-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_negative_rectangle_zero_iff_source_continuous_on_interval
-- name    : AvramDividend.Classical.avram_wave4_04a_actual_intrinsic_negative_rectangle_zero_iff_source_continuous_on_interval
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T19:18:06.731994+00:00
-- url     : https://prove2.me/theorems/edb1adf2-773d-4c79-a346-bf769872de41
-- title:
--   Genuine source Lévy negative jump-counting measure has zero mass exactly on sample-path continuity intervals
-- statement:
--   For every sample of the actual spectrally negative Lévy process X on its original Ω and all times s,t, the intrinsic counting measure of original negative nonzero jumps vanishes on (s,t]×(-∞,0) if and only if that same original sample path is continuous at every point in (s,t]. This all-path, all-interval equality needs neither bounded variation nor finite activity and does not infer a compensator or Poisson law.
-- source:
--   Canonical Proved 4087af7c actual intrinsic negative rectangle zero iff every original jump mark vanishes there, and canonical Proved d98a57fe source nonzero jump iff failure of sample path continuity at each positive time. Every u∈(s,t] has u>0 because s∈ℝ≥0. Pointwise propositional replacement yields the original-path statement with no exceptional sample set or auxiliary Lévy process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_04a_actual_intrinsic_negative_rectangle_zero_iff_source_continuous_on_interval
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (s t : ℝ≥0) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ Iio (0 : ℝ)) = 0 ↔
      ∀ u : ℝ≥0, u ∈ Ioc s t →
        ContinuousAt (fun v : ℝ≥0 => X.X v ω) u := by sorry
