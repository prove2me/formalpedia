-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a24_original_finite_mesh_positive_excess_integrable
-- name    : AvramDividend.Classical.avram_a24_original_finite_mesh_positive_excess_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T16:56:58.277547+00:00
-- url     : https://prove2.me/theorems/36d63834-66d1-4445-b4f0-e85b9f83fe24
-- title:
--   Integrable positive-part residual for a physically centred Gaussian finite mesh
-- statement:
--   For an integrable stopped real reward and a finite family of integrable predictable linear Gaussian gains, integrable Hessian coefficients and their quadratic Gaussian gains, the positive part of the exact signed finite-grid residual is integrable. This establishes the integrability conjunct in the original A24 zero-jump finitecap physical positive-mesh theorem, leaving the substantive stopped Ito-Stieltjes L1 limit to prove.

import Mathlib
open MeasureTheory Set
open scoped BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a24_original_finite_mesh_positive_excess_integrable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (F : Ω → ℝ) (hFI : Integrable F P)
    (a c : ℝ) (S : Finset ℕ) (G H M : ℕ → Ω → ℝ)
    (hGI : ∀ i ∈ S, Integrable (fun ω => G i ω * M i ω) P)
    (hHI : ∀ i ∈ S, Integrable (H i) P)
    (hH2I : ∀ i ∈ S, Integrable (fun ω => H i ω * (M i ω) ^ 2) P) :
    Integrable (fun ω => max (F ω - a -
      ∑ i ∈ S, (G i ω * M i ω +
      (H i ω * (M i ω) ^ 2 - c * H i ω))) 0) P:= by sorry
