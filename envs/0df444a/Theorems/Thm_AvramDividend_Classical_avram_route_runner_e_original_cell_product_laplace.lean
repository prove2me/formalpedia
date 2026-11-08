-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_route_runner_e_original_cell_product_laplace
-- name    : AvramDividend.Classical.avram_route_runner_e_original_cell_product_laplace
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T16:34:00.999493+00:00
-- url     : https://prove2.me/theorems/24421b1f-fecd-43f2-b3f1-1a7ed517d143
-- title:
--   Original strict negative-jump finite cell product is its genuine marked Laplace transform
-- statement:
--   On every original Lévy sample path and arbitrary half-open physical window (s,t], the product of exponentiated negative jump marks below the strict k cutoff equals the exponential of the negative intrinsic weighted marked-jump lintegral. The formula retains time-zero and left-endpoint exclusions. This source-exact bridge permits the physical equal-cell observables to be expressed as shifted future Lévy-path Laplace functionals.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn14_original_cell_weighted_finite_sum
import Theorems.Thm_AvramDividend_Classical_avram_redux19_finite_nonnegative_marked_sum_real_exponential
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_route_runner_e_original_cell_product_laplace
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (s t : ℝ≥0) (k : ℕ) :
    let S : Finset ℝ≥0 :=
      (avram_redux19_original_strict_negative_marked_times_finite X ω t k).toFinset.filter
        (fun u => s < u)
    Real.exp (-((∫⁻ p : ℝ≥0 × ℝ,
      if s < p.1 ∧ p.1 ≤ t ∧ p.2 < -(1 / ((k : ℝ) + 1))
      then ENNReal.ofReal (-p.2) else 0
      ∂((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))).toReal)) =
      ∏ u ∈ S, Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) := by sorry
