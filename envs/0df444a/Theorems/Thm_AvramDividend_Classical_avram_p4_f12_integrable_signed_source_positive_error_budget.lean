-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f12_integrable_signed_source_positive_error_budget
-- name    : AvramDividend.Classical.avram_p4_f12_integrable_signed_source_positive_error_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T00:28:49.837133+00:00
-- url     : https://prove2.me/theorems/6b3ee779-82eb-4188-a6c4-3ac8c69868ce
-- title:
--   Signed Itô source inequality with integrable positive error
-- statement:
--   An integrable payoff bounded almost everywhere by its initial level plus a centred martingale source, a nonpositive-mean generator contribution and an integrable approximation error has expectation bounded by the initial level plus the expectation of the positive part of the error. The estimate isolates the precise error-convergence obligation in stopped Itô grid reductions.
-- source:
--   Bochner integral monotonicity, centred martingale sources and signed physical-grid approximation

import Mathlib
open MeasureTheory
noncomputable section

theorem AvramDividend.Classical.avram_p4_f12_integrable_signed_source_positive_error_budget
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (F M G E : Ω → ℝ)
    (hF : Integrable F P) (hM : Integrable M P)
    (hG : Integrable G P) (hE : Integrable E P)
    (b : ℝ) (hMzero : (∫ ω, M ω ∂P) = 0)
    (hGnonpos : (∫ ω, G ω ∂P) ≤ 0)
    (hSource : ∀ᵐ ω ∂P, F ω ≤ b + M ω + G ω + E ω) :
    (∫ ω, F ω ∂P) ≤ b + ∫ ω, max (E ω) 0 ∂P := by sorry
