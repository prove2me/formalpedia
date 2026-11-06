-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_negative_band_bounded_collision_shorttime_L1_zero
-- name    : AvramDividend.Classical.avram_p4_s3_original_negative_band_bounded_collision_shorttime_L1_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T09:58:06.02155+00:00
-- url     : https://prove2.me/theorems/d5409435-21ef-4e11-94d8-40c1cd6ba1a9
-- title:
--   Actual original bounded collision error vanishes in L1 at small deterministic time scales
-- statement:
--   For the original spectrally negative Lévy process, a fixed separated negative jump band, and any sequence of measurable uniformly bounded random coefficients, the expected norm of the collision-weighted count on the shrinking physical interval (0,T/k] converges to zero. The proof quantifies the error by B times the square of the exact Lévy intensity, uses the original physical count and real-scaled horizon rate, and does not replace any process by an equality-in-law surrogate.
-- source:
--   Depends on new source-exact original physical negative-band weighted collision L1 norm theorem and the already-Proved exact physical horizon rate division theorem c3093fe5-49b3-448a-b97e-e89c4d11ca3b.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_s3_original_negative_band_bounded_collision_shorttime_L1_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (H : ℕ → Ω → ℝ) (hHm : ∀ k, Measurable (H k))
    (B : ℝ) (hB : 0 ≤ B)
    (hH : ∀ k ω, |H k ω| ≤ B) :
    let K : ℕ → Ω → ℕ := fun k ω =>
      {u : ℝ≥0 | 0 < u ∧ u ≤ T / (k : ℝ≥0) ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard
    Filter.Tendsto (fun k : ℕ =>
      ∫ ω, ‖H k ω * (if 2 ≤ K k ω then (K k ω : ℝ) else 0)‖ ∂P)
      Filter.atTop (nhds (0 : ℝ)) := by sorry
