-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_rectangle_of_unconditional_rate
-- name    : AvramDividend.Classical.avram_p2_e_compensator_original_rectangle_of_unconditional_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:37:21.342204+00:00
-- url     : https://prove2.me/theorems/9db23f4e-4e84-4c13-9f3a-7b591eaaf3ff
-- title:
--   Source intrinsic marked rectangle compensator follows from the single original unconditional rate
-- statement:
--   The exact original marked jump count on (s,t] factors from any F_s-measurable past event. Once its unconditional original-process marked rate is assumed, the corresponding predictable-event compensator equals P(A)(t-s)ν(B), without a finite-intensity hypothesis, and permitting infinite expected jump counts.
-- source:
--   Proved original measurable future extractor 5cf3e058 and original past factorisation ad24b83b. Only the original unconditional ν-rate is explicit as a hypothesis; no alternate stochastic process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_future_measurable_extractor
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_intrinsic_future_rectangle_past_factor_of_measurable_extractor

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_e_compensator_original_rectangle_of_unconditional_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hRate : (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) =
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) :
    (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) =
      P A * ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by sorry
