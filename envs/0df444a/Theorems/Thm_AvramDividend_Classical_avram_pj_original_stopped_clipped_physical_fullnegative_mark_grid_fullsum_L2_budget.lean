-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_original_stopped_clipped_physical_fullnegative_mark_grid_fullsum_L2_budget
-- name    : AvramDividend.Classical.avram_pj_original_stopped_clipped_physical_fullnegative_mark_grid_fullsum_L2_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T12:16:36.576635+00:00
-- url     : https://prove2.me/theorems/16e2f749-34af-424b-a999-c18148c8c84b
-- title:
--   Original stopped clipped full negative-mark physical-grid martingale full sum L2 budget from true conditional centring and diagonal isometry
-- statement:
--   Under the genuine original stopped clipped physical-grid diagonal L2 hypotheses, original count integrability, pairwise product integrability and actual strong past-adaptation, the entire sum of compensated full negative-mark increments has expected squared value at most K squared times bounded original horizon n and the true finite negative Levy intensity. The exact original full-sum orthogonality theorem c296efc8 and proven diagonal original L2 certificate e7df4cec combine without replacing the original process or dividend strategy.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_fullnegative_cutoff_adapted_physical_grid_exact_fullsum_L2
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_fullmark_clipped_physical_grid_L2_uniform_energy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_original_stopped_clipped_physical_fullnegative_mark_grid_fullsum_L2_budget
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
    (∀ j ∈ Finset.range m,
      Integrable (fun ω => (N j ω).toReal - r j) P) →
    (∀ i ∈ Finset.range m, ∀ j ∈ Finset.range m,
      Integrable (fun ω => Z i ω * Z j ω) P) →
    (∀ i ∈ Finset.range m, ∀ j ∈ Finset.range m, i < j →
      StronglyMeasurable[𝓕.rightCont (grid j)]
        (fun ω => Z i ω * (if (ρ ω : WithTop ℝ≥0) ≤
          (grid j : WithTop ℝ≥0) then (0 : ℝ) else H j ω))) →
    (∫ ω, (∑ i ∈ Finset.range m, Z i ω)^2 ∂P) ≤
      K^2 * ((n : ℝ) *
        (X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal) := by sorry
