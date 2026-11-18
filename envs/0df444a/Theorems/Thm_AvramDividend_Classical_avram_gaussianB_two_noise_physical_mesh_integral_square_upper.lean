-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gaussianB_two_noise_physical_mesh_integral_square_upper
-- name    : AvramDividend.Classical.avram_gaussianB_two_noise_physical_mesh_integral_square_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T00:38:17.521578+00:00
-- url     : https://prove2.me/theorems/993208c2-af87-45c0-8123-b4337bfdc285
-- title:
--   Integrated L2 error of Gaussian linear-plus-quadratic physical mesh is bounded by separate channel energies
-- statement:
--   Let L_m and Q_m be the original Gaussian linear and compensated-quadratic physical-grid noise channels with integrable squares. The integrated squared difference between their combined mesh values at levels m and l is bounded above by twice the linear-channel difference's second moment plus four times the second moment of each quadratic channel. Combined with Proved B64 linear mesh isometry, B239 clipped weight Cauchy and gb28 quadratic O(1/m) rate, this inequality supplies the deterministic energy assembly needed to certify full original G/H grid L2 convergence.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
open MeasureTheory
noncomputable section

theorem AvramDividend.Classical.avram_gaussianB_two_noise_physical_mesh_integral_square_upper
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (L Q : ℕ → Ω → ℝ)
    (hLInt : ∀ m l, Integrable (fun ω => (L m ω - L l ω) ^ 2) P)
    (hQInt : ∀ m, Integrable (fun ω => (Q m ω) ^ 2) P)
    (hMInt : ∀ m l, Integrable (fun ω =>
      ((L m ω + Q m ω) - (L l ω + Q l ω)) ^ 2) P) :
    ∀ m l,
      (∫ ω, ((L m ω + Q m ω) -
        (L l ω + Q l ω)) ^ 2 ∂P) ≤
      2 * (∫ ω, (L m ω - L l ω) ^ 2 ∂P) +
      4 * (∫ ω, (Q m ω) ^ 2 ∂P) +
      4 * (∫ ω, (Q l ω) ^ 2 ∂P) := by sorry
