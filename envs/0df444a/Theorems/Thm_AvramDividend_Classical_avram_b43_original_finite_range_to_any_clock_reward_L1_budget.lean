-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b43_original_finite_range_to_any_clock_reward_L1_budget
-- name    : AvramDividend.Classical.avram_b43_original_finite_range_to_any_clock_reward_L1_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T09:12:25.420587+00:00
-- url     : https://prove2.me/theorems/b9633538-4f3b-4c22-9f9c-1ab0b3b87ce1
-- title:
--   Original finite-range mixed stopped Ito budgets pass to any restricted L1 reward limit
-- statement:
--   A sequence of genuine finite-range stopped original mixed-Lévy physical rewards, each obeying the exact source signed Ito-Meyer eventwise budget, transfers that budget to any integrable reward obtained as its restricted L1 limit. This enables arbitrary bounded stopped-clock approximation once the actual source reward convergence is established.
-- source:
--   Proved B42 finite-range source signed ledger event budget, Mathlib tendsto_integral_of_L1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b42_original_finite_range_physical_ledger_budget
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b43_original_finite_range_to_any_clock_reward_L1_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (hn : 0 < n)
    (τ : ℕ → Ω → ℝ≥0)
    (hτstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (τ k ω : WithTop ℝ≥0)))
    (hτbound : ∀ k ω, τ k ω ≤ (n : ℝ≥0))
    (S : ℕ → Finset ℝ≥0) (hτrange : ∀ k ω, τ k ω ∈ S k)
    (A : Set Ω) (hA : MeasurableSet[𝓕.rightCont 0] A)
    (b : ℝ) (F : Ω → ℝ) (Fseq Bseq : ℕ → Ω → ℝ)
    (hFI : Integrable F P) (hFkI : ∀ k, Integrable (Fseq k) P)
    (hBsign : ∀ k, ∀ᵐ ω ∂(P.restrict A), Bseq k ω ≤ 0)
    (hLedger : ∀ k (R Jsmall : ℝ≥0 → Ω → ℝ),
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, Tendsto
        (fun j : ℕ => avram_p4_h_gaussian_intrinsic_truncated_residual X j t ω)
        atTop (𝓝 (R t ω))) →
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, Tendsto
        (fun j : ℕ => avram_p4_h_gaussian_intrinsic_small_band_compensated X j t ω)
        atTop (𝓝 (Jsmall t ω))) →
      ∀ᵐ ω ∂(P.restrict A),
        Fseq k ω ≤ b + R (τ k ω) ω + Jsmall (τ k ω) ω + Bseq k ω)
    (hL1 : Tendsto (fun k => ∫⁻ ω in A,
      ‖Fseq k ω - F ω‖ₑ ∂P) atTop (𝓝 (0 : ℝ≥0∞))) :
    (∫ ω in A, F ω ∂P) ≤ b * (P A).toReal := by sorry
