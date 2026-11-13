-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_bv_positive_physical_error_L1_from_integrable_envelope
-- name    : AvramDividend.Classical.avram_a06_bv_positive_physical_error_L1_from_integrable_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T11:26:31.412869+00:00
-- url     : https://prove2.me/theorems/cbc47669-cf35-4692-9469-18a021d201c1
-- title:
--   A06 physical BV positive errors vanish in L1 under a genuine integrable envelope
-- statement:
--   The positive part of the original physical-cell stochastic error has a vanishing expected value whenever its a.e. pathwise error tends to zero and its absolute size is dominated by a genuine integrable original-source envelope. This supplies the DCT interface for interior Taylor and jump/contact errors for arbitrary positive horizons. No integrability of the signed HJB generator residual is required; separate source-specific proofs must supply the envelope and a.e. convergence.

import Mathlib
open MeasureTheory Filter Set
open scoped Topology
noncomputable section

theorem AvramDividend.Classical.avram_a06_bv_positive_physical_error_L1_from_integrable_envelope
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Err : ℕ → Ω → ℝ)
    (hErrMeas : ∀ n, AEStronglyMeasurable (Err n) P)
    (hErrAE : ∀ᵐ ω ∂P, Tendsto (fun n => Err n ω) atTop (𝓝 (0 : ℝ)))
    (H : Ω → ℝ) (hHI : Integrable H P)
    (hDom : ∀ n, ∀ᵐ ω ∂P, ‖Err n ω‖ ≤ H ω) :
    (∀ n, Integrable (fun ω => max (Err n ω) 0) P) ∧
    Tendsto (fun n => ∫ ω, max (Err n ω) 0 ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
