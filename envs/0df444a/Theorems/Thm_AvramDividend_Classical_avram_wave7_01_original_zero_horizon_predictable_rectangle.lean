-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_zero_horizon_predictable_rectangle
-- name    : AvramDividend.Classical.avram_wave7_01_original_zero_horizon_predictable_rectangle
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T12:45:01.458541+00:00
-- url     : https://prove2.me/theorems/dc5d710d-b515-4f79-ba6b-74d9048f5860
-- title:
--   Original intrinsic marked predictable rectangle is exact on a zero-length horizon
-- statement:
--   For any same-time window (s,s] and any Borel mark set B, the original SpectrallyNegativeLevy intrinsic time–mark count vanishes pathwise and its original past-restricted first moment matches the prescribed zero time-gap ν(B) compensation identity. This holds without BV, finite activity or a future extractor premise.
-- source:
--   Zero-horizon boundary case for the exact canonical rectangle compensation target 393b03a8-2e9a-43d8-b415-854d86d58104, preserving all original process and filtration objects.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_original_zero_horizon_predictable_rectangle
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (∫⁻ ω in A,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s s ×ˢ B) ∂P) =
    P A * ((s - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by sorry
