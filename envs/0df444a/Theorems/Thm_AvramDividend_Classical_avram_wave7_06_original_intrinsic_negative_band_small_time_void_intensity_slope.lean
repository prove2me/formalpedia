-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_intrinsic_negative_band_small_time_void_intensity_slope
-- name    : AvramDividend.Classical.avram_wave7_06_original_intrinsic_negative_band_small_time_void_intensity_slope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:46:23.840995+00:00
-- url     : https://prove2.me/theorems/17372d7a-a1d2-4158-9ab7-aa9be61fb864
-- title:
--   Small-time original intrinsic negative-band jump probability has Lévy-rate slope
-- statement:
--   For the actual source X on the original probability space, the probability of at least one intrinsic negative-band jump over the interval (0,T/k] has first-order asymptotic (T/k)ν(B). This source-specific small-time Lévy intensity identification is the substantive unresolved step in turning the already-Proved original void semigroup into its exact Poisson exponential law. No auxiliary sample space or additional hypotheses.
-- source:
--   W7-06 faithful source infinite-divisibility small-time intensity obligation; separate from the already-Proved semigroup and analytic exponential limit; no proof claimed by authoring.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_intrinsic_negative_band_small_time_void_intensity_slope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (n : ℕ) (hT : 0 < T) :
    Filter.Tendsto
      (fun k : ℕ => (k : ℝ) *
        (1 - (P {ω : Ω |
          ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
            (Ioc 0 (T / (k : ℝ≥0)) ×ˢ
              Iic (-(1 / ((n : ℝ) + 1)))) = 0}).toReal))
      Filter.atTop
      (nhds ((T : ℝ) *
        (X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal)) := by sorry
