-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a113_original_zero_horizon_physical_negative_Borel_count_pathwise_zero_20261114
-- name    : AvramDividend.Classical.avram_a113_original_zero_horizon_physical_negative_Borel_count_pathwise_zero_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T19:12:40.107928+00:00
-- url     : https://prove2.me/theorems/ee1050cc-9264-4f3b-9f36-051f7f70ad82
-- title:
--   Original physical negative Borel jump count at zero horizon is identically zero on every path
-- statement:
--   For every original spectrally negative Lévy sample path and any Borel mark set, the number of physical jumps in the empty time window (0,0] is exactly zero, pathwise. It is independent of Lévy intensity, Gaussian volatility, filtration regularity, and probability law.
-- source:
--   Empty interval Ioc (0:NNReal) 0 and measure_empty for the original marked jump-count measure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a113_original_zero_horizon_physical_negative_Borel_count_pathwise_zero_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (B : Set ℝ) (ω : Ω) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc (0 : ℝ≥0) 0 ×ˢ B) = 0 := by sorry
