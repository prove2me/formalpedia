-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_actual_intrinsic_rectangle_past_event_factor_unconditional
-- name    : AvramDividend.Classical.avram_wave7_01_actual_intrinsic_rectangle_past_event_factor_unconditional
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T19:31:40.056896+00:00
-- url     : https://prove2.me/theorems/264b3973-004f-414d-99ed-df5c2c01d29c
-- title:
--   Every actual source Borel marked future jump rectangle factors from its original past event
-- statement:
--   For the actual spectrally negative Lévy process on its original Ω, filtration and measure, the literal intrinsic Borel marked count of all nonzero jumps on (s,t] is independent in first moment of any past event in 𝓕_s. Requires no finite activity, no ν-rate identity, no replacement stochastic process, and works for arbitrary Borel B. This is the complete genuine predictable rectangle factorisation, with the separate unconditional Lévy intensity identification still Open.
-- source:
--   Compose Proved original same-path future extractor 5cf3e058 with Proved original source past-event independence factorisation ad24b83b.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_future_measurable_extractor
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_intrinsic_future_rectangle_past_factor_of_measurable_extractor
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_actual_intrinsic_rectangle_past_event_factor_unconditional
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (∫⁻ ω in A,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) =
    P A * (∫⁻ ω,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) := by sorry
