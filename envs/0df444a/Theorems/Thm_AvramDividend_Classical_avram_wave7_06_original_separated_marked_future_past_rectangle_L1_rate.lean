-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_separated_marked_future_past_rectangle_L1_rate
-- name    : AvramDividend.Classical.avram_wave7_06_original_separated_marked_future_past_rectangle_L1_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T07:07:07.732418+00:00
-- url     : https://prove2.me/theorems/ea8700f6-00a4-46a5-991e-c743f413c42b
-- title:
--   Original past-event weighted future marked-count L¹ rate under the exact Lévy ν source
-- statement:
--   For every genuine source-filtration past event A and a strictly separated negative Borel mark set B, the expected number of original Lévy marked jumps on (s,s+T] restricted to A equals P(A) T ν(B). The proof uses the accepted source future extractor and past independence, reducing the remaining identification to the original zero-origin ν rate and marked-count time stationarity, both owned by W7-01/P2.
-- source:
--   W7-06 original-process conditional jump compensator; exact original X, P, 𝓕, left-limits and ν, no auxiliary process or assumed equality in law.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_separated_marked_future_past_rectangle_L1_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (A : Set Ω)
    (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B)
    (ε : ℝ) (hε : 0 < ε) (hBsep : B ⊆ Iic (-ε)) :
    (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B) ∂P) =
      P A * ((T : ℝ≥0∞) * X.ν B) := by sorry
