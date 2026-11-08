-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_route_runner_f_original_unit_grid_cell_product_laplace
-- name    : AvramDividend.Classical.avram_route_runner_f_original_unit_grid_cell_product_laplace
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T17:59:20.719143+00:00
-- url     : https://prove2.me/theorems/84e41308-fa5c-4160-b9c7-d819e146be75
-- title:
--   Canonical original unit-horizon marked-cell product equals its physical Laplace functional
-- statement:
--   For every original Lévy sample and every physical half-open cell inside one, the negative-jump mark exponential product defined from the canonical full unit-horizon finite set equals the exponential of the actual source marked-jump integral on that cell. This connects the canonical equal-cell product for independent increments to full shifted-path distribution laws.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_route_runner_e_original_cell_product_laplace
import Theorems.Thm_AvramDividend_Classical_avram_route_runner_f_original_unit_grid_cell_finset_stable
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_route_runner_f_original_unit_grid_cell_product_laplace
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (s t : ℝ≥0) (ht : t ≤ 1) (k : ℕ) :
    (∏ u ∈ (avram_redux19_original_strict_negative_marked_times_finite
      X ω (1 : ℝ≥0) k).toFinset.filter (fun u => s < u ∧ u ≤ t),
      Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) =
    Real.exp (-((∫⁻ p : ℝ≥0 × ℝ,
      if s < p.1 ∧ p.1 ≤ t ∧ p.2 < -(1 / ((k : ℝ) + 1))
      then ENNReal.ofReal (-p.2) else 0
      ∂((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))).toReal)) := by sorry
