-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_intrinsic_negative_band_zero_count_law
-- name    : AvramDividend.Classical.avram_wave7_06_original_intrinsic_negative_band_zero_count_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T13:08:18.754056+00:00
-- url     : https://prove2.me/theorems/390a8092-89ae-45c8-bed8-b43b900baa2f
-- title:
--   Exact Poisson zero-count law for genuine original source negative-band jump counting measure
-- statement:
--   On the actual original Lévy probability space, the genuine intrinsic jump counting measure puts zero mass on (0,T] times the negative band at or below -1/(n+1) with the Poisson probability e to minus T times the band's Lévy mass. No auxiliary Poisson process is substituted. Establishing this exact count law is the remaining hard probabilistic step after deterministic event and endpoint conversions have been proved.
-- source:
--   Source-faithful Open child for the published bfc446d3-ff26-4179-a1b4-162efc857227, within mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43. The child asserts the actual source counting-measure law, not an auxiliary canonical model or a conditional assumption. Expected parent reduction uses accepted pathwise d982b66d, left limit f1c48298 and almost-sure horizon endpoint 74159f8b.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_intrinsic_negative_band_zero_count_law
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (n : ℕ) :
    P {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0} =
      ENNReal.ofReal (Real.exp
        (-((T : ℝ) *
          (X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal))) := by sorry
