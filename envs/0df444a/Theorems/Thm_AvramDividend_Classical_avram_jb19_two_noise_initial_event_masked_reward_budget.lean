-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jb19_two_noise_initial_event_masked_reward_budget
-- name    : AvramDividend.Classical.avram_jb19_two_noise_initial_event_masked_reward_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T07:26:36.05372+00:00
-- url     : https://prove2.me/theorems/a1ccf605-c915-47ce-8e29-c1045aa5e550
-- title:
--   Two original-filtration centred noises imply an initial-event stopped dividend budget
-- statement:
--   For an original filtration, if a stopped reward has an almost-sure pathwise upper bounded by initial value plus separately conditionally centred Gaussian and compensated jump noises plus a non-positive residual on an initial event, then its restricted expectation is at most the initial value times the probability of a covering event.
-- source:
--   J-B18 finite mixed physical stopped dividend Itô ledger; an exact algebraic/conditional-expectation transfer for two genuine noise sources.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jb19_two_noise_initial_event_masked_reward_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (E T : Set Ω) (hE : MeasurableSet[m] E) (hET : E ⊆ T)
    (b : ℝ) (hb : 0 ≤ b)
    (R MG MJ B : Ω → ℝ)
    (hRI : Integrable R P)
    (hMGI : Integrable MG P) (hMJI : Integrable MJ P)
    (hMG0 : P[MG | m] =ᵐ[P] 0)
    (hMJ0 : P[MJ | m] =ᵐ[P] 0)
    (hBsign : ∀ᵐ ω ∂(P.restrict E), B ω ≤ 0)
    (hLedger : ∀ᵐ ω ∂(P.restrict E),
      R ω ≤ b + MG ω + MJ ω + B ω) :
    (∫ ω in E, R ω ∂P) ≤ b * (P T).toReal := by sorry
