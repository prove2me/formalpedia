-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18_original_fullmark_finite_range_to_true_clock_L1_cash_budget
-- name    : AvramDividend.Classical.avram_ja18_original_fullmark_finite_range_to_true_clock_L1_cash_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T20:57:40.553195+00:00
-- url     : https://prove2.me/theorems/d84fd794-6536-4d3e-9d91-7499469a7a53
-- title:
--   Actual original fullmark finite-range signed Ito budgets pass to any L1 stopped reward limit
-- statement:
--   For the original finite negative jump activity process, finite-range approximating physical clocks with exact discounted terminal and original full Stieltjes cash, an eventwise source-specific signed Ito inequality using intrinsic Gaussian R and fully compensated negative marks Jfull implies each restricted expected cash budget. Restricted L1 convergence of those original rewards to a true bounded-clock reward transfers the budget, keeping all large negative marks and avoiding Gaussian/retained-smallmark source mismatch.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_ja18_original_finite_range_fullmark_signed_ito_initial_event_budget
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18_original_fullmark_finite_range_to_true_clock_L1_cash_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (q x : ℝ) (w : ℝ → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (hn : 0 < n) (τ : ℕ → Ω → ℝ≥0)
    (hτstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (τ k ω : WithTop ℝ≥0)))
    (hτbound : ∀ k ω, τ k ω ≤ (n : ℝ≥0))
    (S : ℕ → Finset ℝ≥0) (hτrange : ∀ k ω, τ k ω ∈ S k)
    (F : Ω → ℝ) (Fseq : ℕ → Ω → ℝ)
    (hFsource : ∀ k ω, Fseq k ω =
      Real.exp (-(q * (τ k ω : ℝ))) *
        w (if τ k ω = 0 ∨ (τ k ω : ℝ≥0∞) < ruinTime X x D ω
          then x + X.X (τ k ω) ω - rightLimit D (τ k ω) ω
          else riskProcess X x D (τ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFI : Integrable F P)
    (hFkI : ∀ k, Integrable (Fseq k) P)
    (A : Set Ω) (hA : MeasurableSet[𝓕.rightCont 0] A)
    (b : ℝ) (hb : 0 ≤ b)
    (hIto : ∀ k (R Jsmall Jfull : ℝ≥0 → Ω → ℝ),
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
          atTop (nhds (R t ω))) →
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
          atTop (nhds (Jsmall t ω))) →
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Jfull t ω =
          Jsmall t ω + avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω +
          (t : ℝ) * (X.c - ∫ ω, X.X 1 ω ∂P)) →
      ∃ B : Ω → ℝ,
        (∀ᵐ ω ∂(P.restrict A), B ω ≤ 0) ∧
        (∀ᵐ ω ∂(P.restrict A),
          Fseq k ω ≤ b + R (τ k ω) ω + Jfull (τ k ω) ω + B ω))
    (hL1 : Tendsto (fun k => ∫⁻ ω in A,
      ‖Fseq k ω - F ω‖ₑ ∂P) atTop (𝓝 (0 : ℝ≥0∞))) :
    (∫ ω in A, F ω ∂P) ≤ b * (P A).toReal := by sorry
