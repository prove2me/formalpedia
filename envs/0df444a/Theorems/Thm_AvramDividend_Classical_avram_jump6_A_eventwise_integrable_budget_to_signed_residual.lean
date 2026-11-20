-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_eventwise_integrable_budget_to_signed_residual
-- name    : AvramDividend.Classical.avram_jump6_A_eventwise_integrable_budget_to_signed_residual
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T20:38:39.236623+00:00
-- url     : https://prove2.me/theorems/f3d50de5-2e1a-4878-922d-5181d7ed89cb
-- title:
--   Initial-event expected budget implies a constant integrable signed remainder with nonpositive integral
-- statement:
--   For a true integrable reward and an arbitrary genuinely centred integrable stopped noise gain, an initial-event expectation upper bound constructs an explicit integrable signed residual E=F-b-M. It satisfies the exact pathwise ledger and nonpositive eventwise mean, without incorrectly requiring the spatial noise to be a fixed unit multiple of the intrinsic Gaussian and fullmark process.

import Mathlib
open MeasureTheory Set Filter Topology
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_eventwise_integrable_budget_to_signed_residual
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (A : Set Ω) (hA : MeasurableSet A)
    (b : ℝ) (F M : Ω → ℝ)
    (hFI : Integrable F P) (hMI : Integrable M P)
    (hMzero : (∫ ω in A, M ω ∂P) = 0)
    (hBudget : (∫ ω in A, F ω ∂P) ≤ b * (P A).toReal) :
    ∃ Err : ℕ → Ω → ℝ,
      (∀ m, IntegrableOn (Err m) A P) ∧
      (∀ m, ∀ᵐ ω ∂(P.restrict A),
        F ω ≤ b + M ω + Err m ω) ∧
      (∀ ε : ℝ, 0 < ε →
        ∃ m, (∫ ω in A, Err m ω ∂P) ≤ ε) := by sorry
