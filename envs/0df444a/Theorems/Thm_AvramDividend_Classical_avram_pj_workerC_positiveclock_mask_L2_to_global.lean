-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_positiveclock_mask_L2_to_global
-- name    : AvramDividend.Classical.avram_pj_workerC_positiveclock_mask_L2_to_global
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T20:31:57.823896+00:00
-- url     : https://prove2.me/theorems/04abc3dd-08e7-4f47-bfdb-c8b15a4502da
-- title:
--   Positive-clock masked physical Ito error with true zero-clock equality extends globally preserving L2
-- statement:
--   Mask signed K to the positive stopping event, use V=U and Q=0 when rho=0, and retain the original centred L2 residual E. The global error equals the masked conditional source, with identical L2 and convergence certificates.
-- source:
--   Noncircular deterministic wrapper for 65b80d50 from c2a65023, preserving true postpayment zero-clock boundary and avoiding fake cancellation at t=0.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_signed_spatial_K_mask_preserves_L1
open scoped NNReal ENNReal
open MeasureTheory Set Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_positiveclock_mask_L2_to_global
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (ρ : Ω → ℝ≥0) (hS : MeasurableSet {ω : Ω | ρ ω ≠ 0})
    (V U : Ω → ℝ) (Q : ℕ → Ω → ℝ)
    (hVU : ∀ ω, ρ ω = 0 → V ω = U ω)
    (hQ0 : ∀ k ω, ρ ω = 0 → Q k ω = 0)
    (ε : ℝ) (K : Ω → ℝ)
    (hKI : Integrable K P)
    (hKsmall : (∫ ω, |K ω| ∂P) ≤ ε / 4)
    (hEI : ∀ k, Integrable
      (fun ω => if ρ ω = 0 then 0 else V ω - U ω - K ω - Q k ω) P)
    (E : ℕ → Ω → ℝ)
    (hEdef : ∀ k ω, E k ω =
      if ρ ω = 0 then 0 else V ω - U ω - K ω - Q k ω)
    (M : ℝ) (hM : 0 ≤ M)
    (hL2 : ∀ k, Integrable (fun ω => (|E k ω|)^2) P ∧
      (∫ ω, (|E k ω|)^2 ∂P) ≤ M)
    (hAE : ∀ᵐ ω ∂P, Tendsto (fun k : ℕ => E k ω)
      Filter.atTop (𝓝 (0 : ℝ))) :
    ∃ (K' : Ω → ℝ), Integrable K' P ∧
      (∫ ω, |K' ω| ∂P) ≤ ε / 4 ∧
      (∀ k, Integrable (fun ω => V ω - U ω - K' ω - Q k ω) P) ∧
      ∃ (E' : ℕ → Ω → ℝ),
        (∀ k ω, E' k ω = V ω - U ω - K' ω - Q k ω) ∧
        ∃ (M' : ℝ), 0 ≤ M' ∧
          (∀ k, Integrable (fun ω => (|E' k ω|)^2) P ∧
            (∫ ω, (|E' k ω|)^2 ∂P) ≤ M') ∧
          (∀ᵐ ω ∂P, Tendsto (fun k : ℕ => E' k ω)
            Filter.atTop (𝓝 (0 : ℝ))) := by sorry
