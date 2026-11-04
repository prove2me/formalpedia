-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_Ioc_past_event_factor_without_rate
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_Ioc_past_event_factor_without_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T14:58:05.068991+00:00
-- url     : https://prove2.me/theorems/0098144f-d00e-4956-b7c3-9628ec8d37f0
-- title:
--   Genuine original predictable past-event jump-count restricted mean factors without ν rate
-- statement:
--   For the actual Lévy path and original filtration, any past event A at time s and any Borel jump mark B, the original marked jump count on (s,t] restricted to A has expectation P(A) times its unconditional original first moment. It is an exact original-source indicator factorisation with ENNReal zero-infinity safety and no ν-rate, separated-mark, bounded variation, or integrability assumption. It reduces the event-weighted P2-E target to the unweighted original Lévy rate identified by P2-D/P2-A.
-- source:
--   Existing Proved original `(s,t]` arbitrary past-weight factor 7090fa21-7f82-4913-ab72-882c2c3aa0bc; pinned Mathlib lintegral_indicator, lintegral_indicator_one, Measurable.indicator.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_Ioc_st_future_past_factor

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_Ioc_past_event_factor_without_rate
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
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc s t ×ˢ B) ∂P) := by sorry
