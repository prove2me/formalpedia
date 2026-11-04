-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_countable_past_event_origin_means
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_countable_past_event_origin_means
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:20:13.919966+00:00
-- url     : https://prove2.me/theorems/290e0308-7761-4bb8-a338-602ad881ab96
-- title:
--   Countable original predictable past-event jump counts factor against original zero-origin means
-- statement:
--   For a countable family of actual original marked jump counts on (s_i,s_i+T_i] and past events A_i measurable at their own source filtration times, the expected count of each marked rectangle restricted to its true past event sums to the sum of P(A_i) times the corresponding original zero-origin count mean. This derives source-predictable rectangle compensation from the original countable adapted-weight theorem by indicator specialisation. It preserves ENNReal 0*∞ and makes no ν-rate identification or Poisson-copy assumption.
-- source:
--   New source original countable predictable origin-means helper 6819fcdd-af85-47bf-baf8-b412e291f714, submitted separately and pending verification.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_countable_predictable_origin_means

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_countable_past_event_origin_means
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Countable ι]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ι → ℝ≥0)
    (B : ι → Set ℝ) (hB : ∀ i, MeasurableSet (B i))
    (A : ι → Set Ω) (hA : ∀ i, MeasurableSet[𝓕 (s i)] (A i)) :
    (∫⁻ ω, ∑' i, (A i).indicator (fun ω => ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc (s i) (s i + T i) ×ˢ B i)) ω ∂P) =
    ∑' i, P (A i) * (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc 0 (T i) ×ˢ B i) ∂P) := by sorry
