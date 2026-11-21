-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_fullmark_stopped_grid_complete_L2_from_pairwise_crosszero
-- name    : AvramDividend.Classical.avram_pj_workerC_original_fullmark_stopped_grid_complete_L2_from_pairwise_crosszero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T10:13:24.489408+00:00
-- url     : https://prove2.me/theorems/21e86b5c-ca3e-435e-9c4a-5bcf5f7e8776
-- title:
--   Original physical-grid stopped compensated negative-mark full-sum L2 is uniform once distinct original cell cross moments vanish
-- statement:
--   For the actual spectrally negative Lévy path, dividend strategy and original stopped negative-mark physical-grid martingale, distinct-cell compensated cross-product expectations equal to zero suffice for a full finite-grid squared-sum variance at most K squared times horizon times actual finite mark intensity. Original each-cell L2, all cross-product integrability, full diagonal energy and finite-sum orthogonality follow automatically from the Proved platform sources. This leaves exactly the original adapted cross-cell martingale orthogonality as an explicit obligation.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_fullmark_clipped_physical_grid_L2_uniform_energy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_original_fullmark_stopped_grid_complete_L2_from_pairwise_crosszero
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
    (∀ i ∈ Finset.range m, ∀ j ∈ Finset.range m, i ≠ j →
      (∫ ω, Z i ω * Z j ω ∂P) = 0) →
    (∫ ω, (∑ i ∈ Finset.range m, Z i ω)^2 ∂P) ≤
      K^2 * ((n : ℝ) *
        (X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal) := by sorry
