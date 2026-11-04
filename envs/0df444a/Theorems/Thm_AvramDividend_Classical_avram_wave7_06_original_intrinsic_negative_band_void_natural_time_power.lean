-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_intrinsic_negative_band_void_natural_time_power
-- name    : AvramDividend.Classical.avram_wave7_06_original_intrinsic_negative_band_void_natural_time_power
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:47:19.96398+00:00
-- url     : https://prove2.me/theorems/fda6d68f-af4e-4d93-8da7-1864b9d88a1b
-- title:
--   Genuine original negative-band void probability at natural-multiple horizons is a power
-- statement:
--   For the original Lévy process X, the zero-count probability of its actual marked negative-band jump count over (0,kT] equals the k-th power of the void probability over (0,T]. Follows from proved original-filtration independent-increment semigroup and genuine zero-horizon probability, without any auxiliary Poisson space or Lévy-rate assumption.
-- source:
--   W7-06 source-specific repeated-semigroup factor supporting the positive-horizon Poisson rate identification.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_intrinsic_negative_band_void_natural_time_power
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (n k : ℕ) :
    (let p : ℝ≥0 → ENNReal := fun s =>
      P {ω : Ω | ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 s ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0}
     p ((k : ℝ≥0) * T) = (p T) ^ k) := by sorry
