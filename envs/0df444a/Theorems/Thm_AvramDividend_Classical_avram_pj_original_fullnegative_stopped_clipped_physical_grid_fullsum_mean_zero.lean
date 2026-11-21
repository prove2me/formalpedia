-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_original_fullnegative_stopped_clipped_physical_grid_fullsum_mean_zero
-- name    : AvramDividend.Classical.avram_pj_original_fullnegative_stopped_clipped_physical_grid_fullsum_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T16:19:47.047076+00:00
-- url     : https://prove2.me/theorems/ff41c40e-5cdc-474f-b592-09f981a597e7
-- title:
--   Every exact original stopped negative-mark compensated physical grid has globally mean-zero full martingale sum
-- statement:
--   For the genuine original spectrally negative Lévy negative-jump full cutoff marked count and stopped discounted clipped predictable coefficient, each physical cell has zero expected compensator-weighted increment by the proved original conditional centring theorem and strong predictability. The finite full physical-grid sum therefore has exactly zero mean for every horizon, truncation and refinement, with no Gaussian proxy and with true ruin stopping.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_true_future_fullmark_past_predictable_cross_mean_zero_proved
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_complete_negative_mark_cutoff_future_count_integrable
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_each_stopped_clipped_physical_marked_cell_MemLp2
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_stopped_clipped_predictable_coefficient_later_rightCont_stronglyMeasurable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_discounted_deriv_stronglyPredictable
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_original_fullnegative_stopped_clipped_physical_grid_fullsum_mean_zero
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
    (∫ ω, ∑ i ∈ Finset.range m, Z i ω ∂P) = 0 := by sorry
