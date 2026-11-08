-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_turn11_initial_filtration_ae_martingale_budget
-- name    : AvramDividend.Classical.avram_ubv_finite9_turn11_initial_filtration_ae_martingale_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T00:16:18.509804+00:00
-- url     : https://prove2.me/theorems/12ae9b2d-4b40-4887-8130-ce62ff5c0c8d
-- title:
--   Initial-filtration event budgets follow from almost-everywhere domination by a conditionally centred martingale
-- statement:
--   An integrable reward bounded almost everywhere by an initial deterministic benchmark plus an integrable random variable with zero conditional expectation on the initial filtration satisfies the probability-weighted reward upper bound on every initial-filtration measurable event. This all-events version is the final expectation step for the original finite-cap Gaussian stopped source once its physical Ito domination is established.

import Mathlib

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_finite9_turn11_initial_filtration_ae_martingale_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (b : ℝ) (F M : Ω → ℝ)
    (hFI : Integrable F P) (hMI : Integrable M P)
    (hCondZero : ∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P M ω = 0)
    (hUpper : ∀ᵐ ω ∂P, F ω ≤ b + M ω) :
    ∀ (A : Set Ω), MeasurableSet[𝓕.rightCont 0] A →
      (∫ ω in A, F ω ∂P) ≤ b * (P A).toReal := by sorry
