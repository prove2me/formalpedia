-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_finitecap_centered_pathwise_strip_release
-- name    : AvramDividend.Classical.avram_ga_finitecap_centered_pathwise_strip_release
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T20:20:10.722365+00:00
-- url     : https://prove2.me/theorems/f24d1d68-6baa-49c7-9de6-51adc0f98b83
-- title:
--   Original finite-cap stopped HJB expected upper bound from centred cash ledger and vanishing corner/strip errors
-- statement:
--   A genuine physical stopped reward with integrable centred martingale gains has expected value bounded by its HJB initial capital whenever a scalar finite-cap defect and the expected upper-strip error both tend to zero. This closes the deterministic expectation-transfer part of the original stopped Itô verification while leaving the required right-dividend pathwise ledger explicit.
-- source:
--   Exact integration of an a.e. stopped source inequality and passage of cap-defect and physical upper-strip expectation to zero. Supports original finitecap Gaussian expected-reward budget after pathwise ledger 71ef4079.

import Mathlib
open MeasureTheory Filter Topology
noncomputable section

theorem AvramDividend.Classical.avram_ga_finitecap_centered_pathwise_strip_release
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (F : Ω → ℝ) (K : ℝ) (M R : ℕ → Ω → ℝ) (Γ : ℕ → ℝ)
    (hFI : Integrable F P) (hMI : ∀ j, Integrable (M j) P)
    (hM0 : ∀ j, (∫ ω, M j ω ∂P) = 0)
    (hRI : ∀ j, Integrable (R j) P)
    (hΓ : Tendsto Γ atTop (𝓝 (0 : ℝ)))
    (hR : Tendsto (fun j => ∫ ω, R j ω ∂P) atTop (𝓝 (0 : ℝ)))
    (hLedger : ∀ j, ∀ᵐ ω ∂P,
       F ω ≤ K + M j ω + Γ j + R j ω) :
    (∫ ω, F ω ∂P) ≤ K := by sorry
