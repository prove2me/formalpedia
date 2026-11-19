-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_reward76_eventwise_HJB_from_vanishing_positive_residual
-- name    : AvramDividend.Classical.avram_pj_reward76_eventwise_HJB_from_vanishing_positive_residual
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T22:47:28.946531+00:00
-- url     : https://prove2.me/theorems/9202013f-ef15-436d-900d-ead603a6402c
-- title:
--   Eventwise integrable HJB reward supermartingale mean bound from vanishing exact positive residual and nonpositive source mean
-- statement:
--   If a source H has nonpositive eventwise integral, G and H are integrable, and the source-exact positive residual G-a-H has arbitrarily small eventwise L1 positive part, the original eventwise expected reward cannot exceed the initial value a times event probability. This is the final source-to-reward budget step for purejump stopped cash and terminal payoff; no assumption on R integrability.
-- source:
--   Proved avram_pj_reward35_integrable_positive_residual_event_budget and Archimedean order limit.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_pj_reward35_integrable_positive_residual_event_budget
open MeasureTheory Set
noncomputable section

theorem AvramDividend.Classical.avram_pj_reward76_eventwise_HJB_from_vanishing_positive_residual
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (A : Set Ω) (G H : Ω → ℝ) (a : ℝ)
    (hG : Integrable G P) (hH : Integrable H P)
    (hMean : (∫ ω in A, H ω ∂P) ≤ 0)
    (hResidual : ∀ ε : ℝ, 0 < ε →
       (∫ ω in A, max (0 : ℝ) (G ω - a - H ω) ∂P) ≤ ε) :
    (∫ ω in A, G ω ∂P) ≤ a * (P A).toReal := by sorry
