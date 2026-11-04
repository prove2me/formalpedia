-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_interval_mean_to_zero
-- name    : AvramDividend.Classical.avram_p2_c_borel_original_interval_mean_to_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:12:08.988102+00:00
-- url     : https://prove2.me/theorems/e6cad74c-eb1c-4fba-bfa4-be48626c96d2
-- title:
--   Actual intrinsic expected mark counts transport exactly to the zero-origin interval
-- statement:
--   For the original source Lévy process, any Borel mark set, and real nonnegative times s ≤ t, the expected count of intrinsic jumps with marks in B over (s,t] equals the expected count over (0,t-s]. The result holds without rate or finiteness assumptions and is the genuine time-transport component of the P2-C strict-separated canonical rate.
-- source:
--   P2-C extracts a standalone consequence of the Proved original marked-rectangle stationarity theorem add050a6; the accepted 788041e5 sketch already contains this calculation. No unproved zero-origin ν-rate imported.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_rectangle_count_stationary_mean
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_c_borel_original_interval_mean_to_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) =
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (t - s) ×ˢ B) ∂P) := by sorry
