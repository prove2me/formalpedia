-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_intrinsic_negative_band_count_additive_adjacent_horizons
-- name    : AvramDividend.Classical.avram_wave7_06_original_intrinsic_negative_band_count_additive_adjacent_horizons
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:26:23.802779+00:00
-- url     : https://prove2.me/theorems/e3eec394-dbbb-477d-9ef2-3eaad22b4190
-- title:
--   Exact additivity of genuine original intrinsic negative-band counts on adjacent horizons
-- statement:
--   The original X intrinsic marked-jump counting measure of the negative band on (0,T+S] equals its count on (0,T] plus its count on (T,T+S], pathwise for every original ω. This handles boundary cases and does not assume Poisson laws, independence or finite jump count.
-- source:
--   Source-specific interval additivity step for the original future-count and L² increment programme, mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43, supporting open 390a8092-89ae-45c8-bed8-b43b900baa2f.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_intrinsic_negative_band_count_additive_adjacent_horizons
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (T S : ℝ≥0) (n : ℕ) :
    (let NX : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
     let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
     NX (Ioc 0 (T + S) ×ˢ B) =
       NX (Ioc 0 T ×ˢ B) + NX (Ioc T (T + S) ×ˢ B)) := by sorry
