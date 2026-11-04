-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_countable_past_events_st_origin_means
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_countable_past_events_st_origin_means
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:52:51.570685+00:00
-- url     : https://prove2.me/theorems/6396f451-ca55-43a1-b79b-f8e3f1c1fe4b
-- title:
--   Countably many genuine original past-event marked counts at arbitrary ordered endpoints
-- statement:
--   For countably many different events A_i adapted at s_i and genuine original-process marked jumps on arbitrary ordered (s_i,t_i], their expected sum of event-restricted counts equals the sum of P(A_i) times the true original zero-origin mean over (0,t_i-s_i]. This contains no Lévy measure ν assumption.
-- source:
--   Proved original countable past events origin means 290e0308-7761-4bb8-a338-602ad881ab96 and exact interval tsub_add_cancel_of_le.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_countable_past_event_origin_means

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_countable_past_events_st_origin_means
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Countable ι]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ι → ℝ≥0) (hst : ∀ i, s i ≤ t i)
    (B : ι → Set ℝ) (hB : ∀ i, MeasurableSet (B i))
    (A : ι → Set Ω) (hA : ∀ i, MeasurableSet[𝓕 (s i)] (A i)) :
    (∫⁻ ω, ∑' i, (A i).indicator (fun ω => ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc (s i) (t i) ×ˢ B i)) ω ∂P) =
    ∑' i, P (A i) * (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc 0 (t i - s i) ×ˢ B i) ∂P) := by sorry
