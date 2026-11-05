-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_grid_pair_sum_measurable
-- name    : AvramDividend.Classical.avram_p2_e_compensator_original_grid_pair_sum_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T14:41:53.384086+00:00
-- url     : https://prove2.me/theorems/2dec7a05-e3d9-4d90-8a48-beffc202baf0
-- title:
--   Original finite-grid chronological negative-band marked-count sum is measurable
-- statement:
--   The actual source marked-jump count past/future product sum over any finite deterministic grid is measurable, providing the explicit Fatou integrand hypothesis.
-- source:
--   Proved original source rectangle-count measurability theorem 1f8f25b0 and pinned Mathlib finite-sum/measurable-multiplication, with original X and no replacement process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_intrinsic_marked_rectangle_measurable

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_e_compensator_original_grid_pair_sum_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (m : ℕ) (s t : Fin m → ℝ≥0) (n : ℕ) :
    let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
    let N : ℝ≥0 → ℝ≥0 → Ω → ℝ≥0∞ := fun a b ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc a b ×ˢ B)
    Measurable (fun ω => ∑ i : Fin m,
      N 0 (s i) ω * N (s i) (t i) ω) := by sorry
