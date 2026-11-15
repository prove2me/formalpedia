-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a122_original_arbitrary_Borel_mark_void_natural_time_power_20261114
-- name    : AvramDividend.Classical.avram_a122_original_arbitrary_Borel_mark_void_natural_time_power_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T19:30:22.906601+00:00
-- url     : https://prove2.me/theorems/06906c1b-f791-455c-9904-ecd04170a349
-- title:
--   Original physical arbitrary Borel marked-jump void probability at k times a horizon is the kth power of one-horizon void probability
-- statement:
--   For any spectrally negative Lévy process on its original sample space and any Borel marked jump set, the no-jump probability over k repeated equal horizons equals the kth power of its one-horizon probability. This follows from the newly established arbitrary-Borel void multiplicative semigroup A121 and the original pathwise zero-horizon count A113.
-- source:
--   Adapt exact Proved wave7_06_original_intrinsic_negative_band_void_natural_time_power proof, replacing its special cutoff band and semigroup by arbitrary Borel A121 and zero-horizon event A113.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a122_original_arbitrary_Borel_mark_void_natural_time_power_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (k : ℕ) :
    (let p : ℝ≥0 → ℝ≥0∞ := fun s =>
      P {ω : Ω |
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 s ×ˢ B) = 0}
     p ((k : ℝ≥0) * T) = (p T) ^ k) := by sorry
