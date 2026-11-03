-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_intrinsic_negative_band_zero_horizon_measure_univ
-- name    : AvramDividend.Classical.avram_wave7_06_original_intrinsic_negative_band_zero_horizon_measure_univ
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:42:22.45204+00:00
-- url     : https://prove2.me/theorems/b060ebe4-c18b-4e76-a290-35b0faf55637
-- title:
--   Original intrinsic negative-band zero-count event at horizon zero has full source measure
-- statement:
--   For the genuine original intrinsic jump counting measure of the source X, the negative-band count on the empty time rectangle (0,0] is zero on every ω. Consequently its zero-count event has measure P(univ) for arbitrary P. This is the exact zero-horizon base case without assuming probability normalisation.
-- source:
--   Source-faithful T=0 boundary case supporting original negative-band count-law 390a8092-89ae-45c8-bed8-b43b900baa2f, mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_intrinsic_negative_band_zero_horizon_measure_univ
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ) :
    (let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
     P {ω : Ω |
       NX ω (Ioc 0 (0 : ℝ≥0) ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0} =
       P Set.univ) := by sorry
