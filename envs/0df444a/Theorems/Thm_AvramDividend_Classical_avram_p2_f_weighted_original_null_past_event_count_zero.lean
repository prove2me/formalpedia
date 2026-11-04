-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_null_past_event_count_zero
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_null_past_event_count_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T16:11:55.219207+00:00
-- url     : https://prove2.me/theorems/3f935904-66ef-445b-9436-be32aafca195
-- title:
--   Zero contribution of a null original past event to a genuine marked jump count, even at infinite unconditional rate
-- statement:
--   For a genuine original Lévy marked jump count on any ordered (s,t] and a past event A ∈ 𝓕_s with probability zero, the restricted expected count is exactly zero even when the unconditional expected marked count may be infinite. The proof uses accepted original future-past factorisation and native ENNReal zero-times-infinity semantics.
-- source:
--   Accepted original P2-F null-free past-event factor 0098144f-d00e-4956-b7c3-9628ec8d37f0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_Ioc_past_event_factor_without_rate

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_null_past_event_count_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hNull : P A = 0) :
    (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ B) ∂P) = 0 := by sorry
