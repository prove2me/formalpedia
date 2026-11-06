-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_future_negative_borel_rectangle_all_cells
-- name    : AvramDividend.Classical.avram_p4_s3_original_future_negative_borel_rectangle_all_cells
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T09:55:35.676747+00:00
-- url     : https://prove2.me/theorems/5933267b-b40f-483c-a57c-f63294dc12a8
-- title:
--   Original Lévy future negative-Borel rectangles have the exact predictable conditional rate on arbitrary clock cells
-- statement:
--   For the actual jump measure of a spectrally negative Lévy process, every separated negative Borel mark B, every s≤t and every event A measurable at time s, the original count over (s,t]×B has restricted expectation P(A)(t-s)ν(B). This is exactly the uniform physical predictable rectangle compensator required by finite-grid stopped martingale integration, without any extractor or assumed conditional rate.
-- source:
--   Direct full-original-process interval reparametrisation of Proved avram_wave7_06_original_separated_marked_future_past_rectangle_L1_rate (ea8700f6-00a4-46a5-991e-c743f413c42b).

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_original_future_negative_borel_rectangle_all_cells
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (B : Set ℝ) (hB : MeasurableSet B)
    (ε : ℝ) (hε : 0 < ε) (hBsep : B ⊆ Iic (-ε)) :
    ∀ (s t : ℝ≥0), s ≤ t →
      ∀ (A : Set Ω), MeasurableSet[𝓕 s] A →
        (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
            (Ioc s t ×ˢ B) ∂P) =
          P A * (((t - s : ℝ≥0) : ℝ≥0∞)) * X.ν B := by sorry
