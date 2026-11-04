-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_countable_past_events_st_conditional_nu_rates
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_countable_past_events_st_conditional_nu_rates
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T16:03:40.061244+00:00
-- url     : https://prove2.me/theorems/66d991d1-0c20-449c-8c8d-02f44955cddf
-- title:
--   Original countable adapted past-event marked-count compensation on exact ordered intervals conditional on original Lévy rates
-- statement:
--   For original past events A_i ∈ 𝓕_{s_i} and genuine original marked jump counts in (s_i,t_i], the expected countable event-restricted sum equals the sum of P(A_i) times (t_i-s_i) times X.ν(B_i), provided each independent original zero-origin ν-rate identity is separately supplied explicitly.
-- source:
--   Proved original countable exact-interval past-event zero-origin means 6396f451-ca55-43a1-b79b-f8e3f1c1fe4b.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_countable_past_events_st_origin_means

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_countable_past_events_st_conditional_nu_rates
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Countable ι]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ι → ℝ≥0) (hst : ∀ i, s i ≤ t i)
    (B : ι → Set ℝ) (hB : ∀ i, MeasurableSet (B i))
    (A : ι → Set Ω) (hA : ∀ i, MeasurableSet[𝓕 (s i)] (A i))
    (hOrigin : ∀ i, (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc 0 (t i - s i) ×ˢ B i) ∂P) = (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i))) :
    (∫⁻ ω, ∑' i, (A i).indicator (fun ω => ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc (s i) (t i) ×ˢ B i)) ω ∂P) =
    ∑' i, P (A i) * (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)) := by sorry
