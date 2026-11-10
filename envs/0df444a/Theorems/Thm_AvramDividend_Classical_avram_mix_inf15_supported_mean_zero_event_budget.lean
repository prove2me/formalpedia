-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_inf15_supported_mean_zero_event_budget
-- name    : AvramDividend.Classical.avram_mix_inf15_supported_mean_zero_event_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T12:49:24.25276+00:00
-- url     : https://prove2.me/theorems/9a0e71a4-ad46-41ad-9744-9820275ced84
-- title:
--   Supported mean-zero witness transfers an almost-everywhere stopped reward upper bound to the masked budget
-- statement:
--   For a probability measure and measurable event A, a global integrable centred witness M supported almost everywhere on A converts an almost-everywhere reward inequality F ≤ b+M into E[F 1_A] ≤ b P(A). This is the support-based transfer needed for an original mixed stopped Ito-Meyer witness with exact zero-clock cancellation; conditional expectation centring is not assumed.
-- source:
--   Avram mixed infinite-activity positive-clock theorem f5e6e083-f096-4425-bd07-f6a0e0cb10a0, paired with original physical stopped centred witness proposal. Elementary noncircular eventwise integral bridge; hMoff must be proved from original stopping clock 0 convention.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_inf15_supported_mean_zero_event_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (A : Set Ω) (hA : MeasurableSet A)
    (b : ℝ) (F M : Ω → ℝ)
    (hFI : Integrable F P) (hMI : Integrable M P)
    (hMzero : (∫ ω, M ω ∂P) = 0)
    (hMoff : ∀ᵐ ω ∂P, ω ∉ A → M ω = 0)
    (hUpper : ∀ᵐ ω ∂P, F ω ≤ b + M ω) :
    (∫ ω in A, F ω ∂P) ≤ b * (P A).toReal := by sorry
