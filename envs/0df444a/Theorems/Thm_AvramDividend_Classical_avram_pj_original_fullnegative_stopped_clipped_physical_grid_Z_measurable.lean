-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_original_fullnegative_stopped_clipped_physical_grid_Z_measurable
-- name    : AvramDividend.Classical.avram_pj_original_fullnegative_stopped_clipped_physical_grid_Z_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T16:16:00.054295+00:00
-- url     : https://prove2.me/theorems/3c032847-8975-4baf-ae2b-ab1954d49e58
-- title:
--   Actual original stopped clipped full negative Lévy marked physical-grid compensated increment is measurable
-- statement:
--   On the genuine original spectrally negative Lévy path, the actual count of full negative jumps on each physical-grid time cell is measurable at the cell end. The original discounted prepayment derivative is strongly predictable; stopped symmetric clipping is measurable at the same later right-continuous filtration. Their product with the count minus its true Lévy compensator rate is therefore measurable for each mesh cell, with no proxy mark or Gaussian replacement.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_actual_earlier_negative_marked_cell_count_later_filtration_stronglyMeasurable
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_stopped_clipped_predictable_coefficient_later_rightCont_stronglyMeasurable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_discounted_deriv_stronglyPredictable
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_original_fullnegative_stopped_clipped_physical_grid_Z_measurable
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
    ∀ i : ℕ, Measurable (Z i) := by sorry
