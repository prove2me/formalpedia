-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gaussianB_full_GH_mesh_energy_cauchy_of_source_linear_isometry_and_quadratic_rate
-- name    : AvramDividend.Classical.avram_gaussianB_full_GH_mesh_energy_cauchy_of_source_linear_isometry_and_quadratic_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T00:53:46.059345+00:00
-- url     : https://prove2.me/theorems/85b94339-1b0f-4212-813f-35206e681a29
-- title:
--   Original Gaussian stopped G/H grid energy is L2 Cauchy from linear-grid isometry and compensated quadratic 1/m rate
-- statement:
--   Let the original stopped Gaussian physical G/H grid be decomposed into the linear martingale grid L_m and compensated quadratic grid Q_m. If the certified B64 exact isometry identifies the linear difference second moment as σ² times a two-mesh coefficient energy K(m,l) that converges to zero by the B239 occupation theorem, and the certified gb28 variance rate bounds each quadratic second moment by C/(m+1), the entire G/H grid has second-moment two-mesh Cauchy convergence. This closes the algebraic assembly dependency for original positive-drift stopped cash without assuming a result about the wrong Gaussian model.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_quadratic_grid_L2_rate_forces_zero_energy
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_original_two_channel_L2_mesh_second_moment_cauchy
open Filter MeasureTheory AvramDividend.Classical
open scoped Topology
noncomputable section

theorem AvramDividend.Classical.avram_gaussianB_full_GH_mesh_energy_cauchy_of_source_linear_isometry_and_quadratic_rate
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (L Q : ℕ → Ω → ℝ) (K : ℕ × ℕ → ℝ)
    (σ C : ℝ) (hC : 0 ≤ C)
    (hLInt : ∀ m l, Integrable (fun ω => (L m ω - L l ω) ^ 2) P)
    (hQInt : ∀ m, Integrable (fun ω => (Q m ω) ^ 2) P)
    (hMInt : ∀ m l, Integrable (fun ω =>
      ((L m ω + Q m ω) - (L l ω + Q l ω)) ^ 2) P)
    (hLISO : ∀ m l,
      (∫ ω, (L m ω - L l ω) ^ 2 ∂P) = σ ^ 2 * K (m, l))
    (hK : Tendsto K atTop (𝓝 (0 : ℝ)))
    (hQNonneg : ∀ m, 0 ≤ ∫ ω, (Q m ω) ^ 2 ∂P)
    (hQRate : ∀ m,
      (∫ ω, (Q m ω) ^ 2 ∂P) ≤ C / ((m + 1 : ℕ) : ℝ)) :
    Tendsto (fun nm : ℕ × ℕ =>
      ∫ ω, ((L nm.1 ω + Q nm.1 ω) -
        (L nm.2 ω + Q nm.2 ω)) ^ 2 ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
