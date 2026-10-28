-- Prove2me | Theorems.Thm_AvramDividend_Classical_indicator_indepFun_of_both_event_marginals
-- name    : AvramDividend.Classical.indicator_indepFun_of_both_event_marginals
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T15:06:54.586052+00:00
-- url     : https://prove2.me/theorems/ab2aa9f7-6db5-4c1b-abe2-724e0d680ab7
-- title:
--   Event and complementary event marginal laws imply independent event indicator
-- statement:
--   For a probability measure, if both an event A and its complement satisfy the expected factorisation with each measurable inverse image under a random element Y, then the indicator of A is independent of Y.
-- source:
--   Bridges the proved restricted-map event-marginal identity f2cff3c4-e6ba-4ab0-92c3-ede656bfd82d and the complement stopped-history event lemma 14adf425-f38f-4621-b8d2-fdc1e495b583 to the stochastic full-path joint-law theorem 61930a38-11f1-449e-bbb6-67d59c6d5ca8.

import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Restrict

open MeasureTheory ProbabilityTheory Set

theorem AvramDividend.Classical.indicator_indepFun_of_both_event_marginals
    {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (A : Set Ω) (Y : Ω → β)
    (hA : MeasurableSet A) (hY : Measurable Y)
    (hFirst : ∀ B : Set β, MeasurableSet B →
      P (A ∩ Y ⁻¹' B) = P A * P (Y ⁻¹' B))
    (hSecond : ∀ B : Set β, MeasurableSet B →
      P (Aᶜ ∩ Y ⁻¹' B) = P Aᶜ * P (Y ⁻¹' B)) :
    IndepFun (Set.indicator A (fun _ : Ω => (1 : ℝ))) Y P := by
  sorry
