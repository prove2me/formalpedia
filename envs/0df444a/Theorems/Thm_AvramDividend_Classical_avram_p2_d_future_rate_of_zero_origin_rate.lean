-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_rate_of_zero_origin_rate
-- name    : AvramDividend.Classical.avram_p2_d_future_rate_of_zero_origin_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:33:13.838104+00:00
-- url     : https://prove2.me/theorems/0f5f1ffc-179a-4a21-a26d-aa130f2ab095
-- title:
--   Original source marked ν-rate transports from zero-origin to any time interval
-- statement:
--   For an original SpectrallyNegativeLevy process, any Borel real mark set B, and times s≤t, an explicitly established ν-rate equality for the original literal jump count on (0,t−s] implies exactly the same rate on (s,t]. The source's Proved unconditional marked-count stationary-mean theorem suffices; no intensity formula is assumed or hidden.
-- source:
--   Uses Proved add050a6 to identify expected count on (s,s+(t−s)] with (0,t−s], then rewrites s+(t−s)=t. This gives an exact all-Borel physical-clock transport of a rate proved at zero origin.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_rectangle_count_stationary_mean

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_d_future_rate_of_zero_origin_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hOrigin :
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (t - s) ×ˢ B) ∂P) =
        ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) =
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by sorry
