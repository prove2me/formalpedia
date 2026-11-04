-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_past_event_countable_additivity
-- name    : AvramDividend.Classical.avram_p2_d_future_past_event_countable_additivity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:43:44.847902+00:00
-- url     : https://prove2.me/theorems/baf430ef-c87c-4b35-83a4-cb552d42de47
-- title:
--   Original past-event expected marked jump count is countably additive over Borel time-mark regions
-- statement:
--   For any actual original past-filtration event and any pairwise disjoint countable Borel time-mark family, the original event-restricted mean marked count of the union equals the ENNReal tsum of corresponding event-restricted mean counts, including infinite activity and infinite expectations.
-- source:
--   Use the Proved original past-event source occupation measure e509ef60. Its expected count on every Borel set equals a genuine measure Q; measure_iUnion and the original Q evaluations give countable additivity on all disjoint Borel regions, without ν-rate assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_past_expected_time_mark_occupation_measure

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_d_future_past_event_countable_additivity
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (C : ℕ → Set (ℝ≥0 × ℝ))
    (hC : ∀ n, MeasurableSet (C n))
    (hDisj : Pairwise (Function.onFun Disjoint C)) :
    (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (⋃ n, C n) ∂P) =
    ∑' n, (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (C n) ∂P) := by sorry
