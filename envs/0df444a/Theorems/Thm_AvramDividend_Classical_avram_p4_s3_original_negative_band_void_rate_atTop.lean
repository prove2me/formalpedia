-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_negative_band_void_rate_atTop
-- name    : AvramDividend.Classical.avram_p4_s3_original_negative_band_void_rate_atTop
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T07:54:19.17103+00:00
-- url     : https://prove2.me/theorems/84aeadc6-e2c0-489e-81b9-699b0413bae7
-- title:
--   Physical small-time negative-band jump occurrence has the original Lévy rate
-- statement:
--   For the actual jumps of the original spectrally negative Lévy process, the probability of at least one jump in a fixed separated negative mark band during (0,1/k] is asymptotically the band Lévy intensity divided by k. This is derived from accepted exact original first and second factorial moments and Bonferroni bounds, with no equality-in-law replacement.
-- source:
--   Original source exact 604dfce2-720c-427f-b655-b2548c554962 and analytical squeeze 6d362474-4717-43c2-b2a8-f1247b0bf970; Avram Palmowski Pistorius spectrally negative Levy process original jump measure.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_p4_s3_original_negative_band_void_rate_atTop
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ)
    (hν : X.ν (Iic (-(1 / ((n : ℝ) + 1)))) < ⊤) :
    Filter.Tendsto
      (fun k : ℕ => (k : ℝ) * P.real {ω : Ω |
        {u : ℝ≥0 | 0 < u ∧ u ≤ (k : ℝ≥0)⁻¹ ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
            -(1 / ((n : ℝ) + 1))}.ncard ≠ 0})
      Filter.atTop
      (nhds ((X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal)) := by sorry
