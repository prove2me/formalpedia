-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_reward77_tolerance_dependent_compensated_source_eventwise_budget
-- name    : AvramDividend.Classical.avram_pj_reward77_tolerance_dependent_compensated_source_eventwise_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T22:48:50.574014+00:00
-- url     : https://prove2.me/theorems/18b84177-a9da-417e-ac7d-048b7ad88767
-- title:
--   Initial-event reward HJB bound with epsilon-dependent stopped compensated negative-jump source
-- statement:
--   For each positive tolerance the original stopped source may use a different spatial compact band and small negative-jump cutoff, hence a different integrable source H_epsilon. If every such source has nonpositive mean on the initial event and controls the exact eventwise positive reward residual by epsilon, the expected original reward is bounded by its initial value. Avoids an invalid interchange of quantifiers that would demand a single fixed source.
-- source:
--   Original purejump Proposition 4(i) expected reward closure, via Proved avram_pj_reward35_integrable_positive_residual_event_budget and Archimedean order.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_pj_reward35_integrable_positive_residual_event_budget
open MeasureTheory Set
noncomputable section

theorem AvramDividend.Classical.avram_pj_reward77_tolerance_dependent_compensated_source_eventwise_budget
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (A : Set Ω) (G : Ω → ℝ) (a : ℝ)
    (hG : Integrable G P)
    (hSources : ∀ ε : ℝ, 0 < ε →
      ∃ H : Ω → ℝ,
        Integrable H P ∧ (∫ ω in A, H ω ∂P) ≤ 0 ∧
        (∫ ω in A, max (0 : ℝ) (G ω - a - H ω) ∂P) ≤ ε) :
    (∫ ω in A, G ω ∂P) ≤ a * (P A).toReal := by sorry
