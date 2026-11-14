-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b47_original_any_bounded_clock_mixed_ledger_L1_condexp_bridge
-- name    : AvramDividend.Classical.avram_b47_original_any_bounded_clock_mixed_ledger_L1_condexp_bridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T09:13:57.537335+00:00
-- url     : https://prove2.me/theorems/ea7e9e46-daca-4cad-a03e-a7a41f047411
-- title:
--   Original bounded stopped mixed Ito conditional budget from genuine finite grid ledgers and L1 approximation
-- statement:
--   For any bounded right-continuous original Levy stopping clock, construct finite-valued adapted upper grids converging pathwise. If exact original finite-grid stopped reward approximations satisfy an almost surely nonpositive physical HJB/dividend loss, a signed Ito-Meyer upper ledger with intrinsic Gaussian and compensated negative-jump source limits, and restricted L1 convergence on every initial event, then their full-clock reward has conditional expectation at most its initial candidate.
-- source:
--   Proved ja18 original finite stopping grids, B42 original finite-grid signed HJB ledger budget, ubv_finite14 event budgets to F0 conditional expectation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b42_original_finite_range_physical_ledger_budget
import Theorems.Thm_AvramDividend_Classical_avram_ja18_original_rightcont_upper_grid_stops
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite14_initial_event_budget_to_condexp
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b47_original_any_bounded_clock_mixed_ledger_L1_condexp_bridge
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτbound : ∀ ω, τ ω ≤ (n : ℝ≥0))
    (F : Ω → ℝ) (hFI : Integrable F P) (b : ℝ) :
    ∃ (ρ : ℕ → Ω → ℝ≥0) (S : ℕ → Finset ℝ≥0),
      (∀ k, IsStoppingTime 𝓕.rightCont
        (fun ω => (ρ k ω : WithTop ℝ≥0))) ∧
      (∀ k ω, ρ k ω ∈ S k) ∧
      (∀ k ω, τ ω ≤ ρ k ω ∧ ρ k ω ≤ (n : ℝ≥0)) ∧
      (∀ ω, Tendsto (fun k => ρ k ω) atTop (𝓝 (τ ω))) ∧
      ∀ (Fseq Bseq : ℕ → Ω → ℝ),
        (∀ k, Integrable (Fseq k) P) →
        (∀ k, ∀ᵐ ω ∂P, Bseq k ω ≤ 0) →
        (∀ k (R Jsmall : ℝ≥0 → Ω → ℝ),
          (∀ᵐ ω ∂P, ∀ t : ℝ≥0, Tendsto
            (fun j : ℕ =>
              avram_p4_h_gaussian_intrinsic_truncated_residual X j t ω)
            atTop (𝓝 (R t ω))) →
          (∀ᵐ ω ∂P, ∀ t : ℝ≥0, Tendsto
            (fun j : ℕ =>
              avram_p4_h_gaussian_intrinsic_small_band_compensated X j t ω)
            atTop (𝓝 (Jsmall t ω))) →
          ∀ᵐ ω ∂P,
            Fseq k ω ≤ b + R (ρ k ω) ω + Jsmall (ρ k ω) ω + Bseq k ω) →
        (∀ A : Set Ω, MeasurableSet[𝓕.rightCont 0] A →
          Tendsto (fun k => ∫⁻ ω in A,
            ‖Fseq k ω - F ω‖ₑ ∂P)
            atTop (𝓝 (0 : ℝ≥0∞))) →
        ∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P F ω ≤ b := by sorry
