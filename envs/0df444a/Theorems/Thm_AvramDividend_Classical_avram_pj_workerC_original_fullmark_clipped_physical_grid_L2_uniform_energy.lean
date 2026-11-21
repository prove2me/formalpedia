-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_fullmark_clipped_physical_grid_L2_uniform_energy
-- name    : AvramDividend.Classical.avram_pj_workerC_original_fullmark_clipped_physical_grid_L2_uniform_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T08:32:14.058186+00:00
-- url     : https://prove2.me/theorems/e7df4cec-3006-4d3b-95e4-36923a3fed5f
-- title:
--   Original true stopped negative Lévy marked physical-grid diagonal L2 energy uniformly bounded by full finite-mark intensity and horizon
-- statement:
--   For the original spectrally negative Lévy process and actual stopped predictable clipped negative-mark counting martingale, the Proved exact diagonal second-moment isometry, clipped coefficient bound and exact original mesh cell rate yield a uniform in physical-grid refinement L2 energy bound of K squared times n times the actual mark intensity. Integrability of the bounded stopped square coefficients is explicitly required; the full negative mark measure and genuine horizon are retained.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_true_uniform_physical_stopped_discounted_negative_mark_diagonal_L2_energy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_fullmark_grid_isometry_and_intensity_uniform_variance
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_finite_mark_physical_grid_rate_uniform_bound
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_uniform_physical_finite_mark_cell_rate_identity
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_original_fullmark_clipped_physical_grid_L2_uniform_energy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q K : ℝ) (hK : 0 ≤ K)
    (cut : ℕ) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (n m : ℕ) (hn : 0 < n) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let grid : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let N : ℕ → Ω → ℝ≥0∞ := fun i ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (grid i) (grid (i + 1)) ×ˢ Iic (-(1 / ((cut : ℝ) + 1))))
    let r : ℕ → ℝ := fun i =>
      (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
        X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal
    let H : ℕ → Ω → ℝ := fun i ω =>
      max (-K) (min K (Real.exp (-(q * (grid i : ℝ))) *
        deriv w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω)
          (grid i))))
    let Z : ℕ → Ω → ℝ := fun i ω =>
      (if (ρ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
        then (0 : ℝ) else H i ω) * ((N i ω).toReal - r i)
    (∀ i ∈ Finset.range m,
      Integrable (fun ω =>
        (if (ρ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
          then (0 : ℝ) else H i ω)^2) P) →
    (∫ ω, ∑ i ∈ Finset.range m, (Z i ω)^2 ∂P) ≤
      K^2 * ((n : ℝ) *
        (X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal) := by sorry
