-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_original_future_fullnegative_mark_grid_stopclipped_cross_weight_stronglyMeasurable
-- name    : AvramDividend.Classical.avram_pj_original_future_fullnegative_mark_grid_stopclipped_cross_weight_stronglyMeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T12:32:03.735198+00:00
-- url     : https://prove2.me/theorems/c859f6d6-b5b0-42be-87ce-36967bc40f85
-- title:
--   Exact original stopped full negative-mark grid earlier compensated cell times later clipped predictable derivative is strongly measurable in later filtration
-- statement:
--   For the genuine original spectrally negative Lévy process and physical nondecreasing grid, each earlier compensated actual full negative-mark jump count times its true stopped clipped predictable weight, multiplied by any later stopped clipped predictable weight, is strongly measurable at the later physical time in the original right-continuous filtration. Follows by combining true past marked-cell count endpoint measurability with stopped clipped predictable coefficient adaptedness, without modifying the Lévy process, jump measure or dividend clock.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_actual_earlier_negative_marked_cell_count_later_filtration_stronglyMeasurable
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_stopped_clipped_predictable_coefficient_later_rightCont_stronglyMeasurable
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_original_future_fullnegative_mark_grid_stopclipped_cross_weight_stronglyMeasurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (cut m : ℕ) (grid : ℕ → ℝ≥0)
    (hGrid : Monotone grid)
    (N : ℕ → Ω → ℝ≥0∞)
    (hActual : ∀ i, N i = fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim
            (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (grid i) (grid (i + 1)) ×ˢ
          Iic (-(1 / ((cut : ℝ) + 1)))))
    (r : ℕ → ℝ)
    (Y : ℝ≥0 → Ω → ℝ)
    (hY : IsStronglyPredictable 𝓕.rightCont Y)
    (K : ℝ) (hK : 0 ≤ K)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (Z : ℕ → Ω → ℝ)
    (hZ : ∀ i ω, Z i ω =
      (if (ρ ω : WithTop ℝ≥0) ≤
        (grid i : WithTop ℝ≥0) then (0 : ℝ)
      else max (-K) (min K (Y (grid i) ω))) *
        ((N i ω).toReal - r i)) :
    ∀ i ∈ Finset.range m, ∀ j ∈ Finset.range m, i < j →
      StronglyMeasurable[𝓕.rightCont (grid j)] (fun ω =>
        Z i ω * (if (ρ ω : WithTop ℝ≥0) ≤
          (grid j : WithTop ℝ≥0) then (0 : ℝ)
        else max (-K) (min K (Y (grid j) ω)))) := by sorry
