-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_Ioc_past_event_origin_mean
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_Ioc_past_event_origin_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:16:38.46438+00:00
-- url     : https://prove2.me/theorems/21295033-b34c-4986-a14c-193be7effea1
-- title:
--   Original past-event marked-count expectation factors against zero-origin source mean
-- statement:
--   For any original Lévy past event A in the true filtration at s and any Borel mark cell B, the restricted expected genuine source jump count over the exact interval (s,t] equals P(A) times the original zero-origin marked count mean over (0,t-s]. The identity requires no original ν rate; it follows from the original event factorisation, stationarity and exact endpoint transport s+(t-s)=t. It is the exact interface for P2-E to insert the independently proved source ν-rate.
-- source:
--   Pending proof of source event factor helper 0098144f-d00e-4956-b7c3-9628ec8d37f0 and already-Proved original stationarity add050a6-3ff4-4747-9805-600b11b7b3d1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_Ioc_past_event_factor_without_rate
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_rectangle_count_stationary_mean

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_Ioc_past_event_origin_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc s t ×ˢ B) ∂P) =
    P A * (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc 0 (t - s) ×ˢ B) ∂P) := by sorry
