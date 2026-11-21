-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_original_stopped_fullnegative_marked_grid_fullsum_uniform_L1_budget
-- name    : AvramDividend.Classical.avram_pj_original_stopped_fullnegative_marked_grid_fullsum_uniform_L1_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T16:22:05.304018+00:00
-- url     : https://prove2.me/theorems/6faab04c-661e-40c8-bfa8-e45b2081afab
-- title:
--   True original stopped full negative Lévy marked physical-grid complete martingale L1 uniform square-root budget
-- statement:
--   For the actual original spectrally negative Lévy negative-mark compensated physical-grid martingale, full sum (not merely diagonal) has L1 norm at most K times the square root of horizon n times genuine finite-cutoff negative-mark intensity. Combine proved fullsum isometry/L2 uniform bound, proved strong measurability of every true stopped clipped physical cell, proved MemLp2 pairwise cross-product integrability, and the full-grid L2 to L1 transfer.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_fullnegative_stopped_clipped_physical_grid_Z_measurable
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_each_stopped_clipped_physical_marked_cell_MemLp2
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_marked_grid_L2_each_cell_implies_all_cross_products_integrable
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_fullnegative_stopped_clipped_physical_grid_martingale_uniform_L2_no_extra_hypotheses
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_physical_fullmark_grid_cross_integrable_L2_budget_gives_L1
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_original_stopped_fullnegative_marked_grid_fullsum_uniform_L1_budget
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
    (∫ ω, |∑ i ∈ Finset.range m, Z i ω| ∂P) ≤
      Real.sqrt (K^2 * ((n : ℝ) *
        (X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal)) := by sorry
