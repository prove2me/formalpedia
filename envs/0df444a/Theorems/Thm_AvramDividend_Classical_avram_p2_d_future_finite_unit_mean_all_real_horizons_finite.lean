-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_finite_unit_mean_all_real_horizons_finite
-- name    : AvramDividend.Classical.avram_p2_d_future_finite_unit_mean_all_real_horizons_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T19:30:48.937562+00:00
-- url     : https://prove2.me/theorems/243bfabc-eb26-4d5a-a9c4-928b60473fd0
-- title:
--   Finite original unit-time marked expectation implies finite expectation at every real horizon
-- statement:
--   For the exact spectrally negative Lévy sample path and Borel mark set B, if the literal original marked jump count has finite expected number over the first unit horizon, it has finite expectation at every finite nonnegative real time, with no finite-activity assumption. This isolates the finite-valued branch needed for a real-time linearity theorem.
-- source:
--   Uses Proved original integer-horizon count mean envelope 98eca88c-b128-4d3f-8561-62cf92f4fe73 plus the Archimedean upper bound of t by a natural n and the ENNReal fact that a product of finite values is finite. ν remains unidentified.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_d_future_finite_unit_mean_all_real_horizons_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (B : Set ℝ) (hB : MeasurableSet B)
    (t : ℝ≥0)
    (hunit : (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (1 : ℝ≥0) ×ˢ B) ∂P) < ⊤) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 t ×ˢ B) ∂P) < ⊤ := by sorry
