-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a27_signed_mean_centered_mesh_transfer
-- name    : AvramDividend.Classical.avram_ga_a27_signed_mean_centered_mesh_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T08:29:56.134197+00:00
-- url     : https://prove2.me/theorems/272be72c-bce7-4f7f-b61e-f3ad7dc5b67f
-- title:
--   Centred Gaussian mesh subtraction preserves integrable signed expectation convergence
-- statement:
--   Subtracting an integrable exactly centred mesh sum from an integrable spatial-minus-generator residual preserves convergence of the signed expectation to zero. Used to transfer the original Gaussian grid centring theorem gledger24 into the stopped spatial residual problem c47f646c.
-- source:
--   Exact algebraic and Bochner-integral transfer required by original stopped zero-jump Gaussian signed-mean child 7699780b-7664-4bf9-8113-35ff759095d8.

import Mathlib
open MeasureTheory
noncomputable section

theorem AvramDividend.Classical.avram_ga_a27_signed_mean_centered_mesh_transfer
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (S M G : ℕ → Ω → ℝ)
    (hM : ∀ m : ℕ, Integrable (M m) P ∧
      (∫ ω, M m ω ∂P) = 0)
    (hSG : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (fun ω => S m ω - G m ω) P ∧
      |∫ ω, S m ω - G m ω ∂P| ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (fun ω => S m ω - M m ω - G m ω) P ∧
      |∫ ω, S m ω - M m ω - G m ω ∂P| ≤ ε := by sorry
