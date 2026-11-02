-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_uniform_interior_cutoffs_with_favourable_kinks
-- name    : AvramDividend.Classical.avram_wave5_05_ubv_uniform_interior_cutoffs_with_favourable_kinks
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:42:23.913193+00:00
-- url     : https://prove2.me/theorems/ec67fc5b-4a84-433d-b8f3-4fd0edc79443
-- title:
--   One sequence of uniformly convergent strictly interior cap localisations has a favourable finite kink at every stage
-- statement:
--   For a finite positive cap, verification candidate continuous on nonnegative reserve values and C2 with derivative at least one only at strictly interior 0<y<c, construct a single sequence of cutoffs b_n in (0,c) with cap gap and global value error each less than 1/(n+1). For every n the slope-one extension at b_n has precise left and right within derivatives w'(b_n) and 1, hence a finite nonpositive derivative jump 1-w'(b_n). This supplies valid localisation and the favourable sign of candidate local-time terms without assuming any derivative exists at c. It does not assert a stochastic chain rule or control the thin-strip compensated generator residual.
-- source:
--   Proved countable globally uniform cap-proximate cutoffs 6074cc01-ba22-43b9-9956-11ce26dbdf08, Proved one-sided Tanaka kink calculus 77c45309-0198-4d37-9809-6702c726442f, inclusive cap secant 44b01929-5817-44ac-9439-6eb3c9879f2c, canonical core unchanged 429e17ca-5528-40b5-b593-7c03973d0706.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_cap_corner_countable_uniform_cutoff_sequence_with_cap_proximity
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_interior_cap_cutoff_one_sided_derivatives_favourable_kink

open MeasureTheory Set Topology Filter AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_wave5_05_ubv_uniform_interior_cutoffs_with_favourable_kinks
    (w : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ENNReal.ofReal c})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < ENNReal.ofReal c → 1 ≤ deriv w y) :
    ∃ b : ℕ → ℝ,
      (∀ n : ℕ, 0 < b n ∧ b n < c ∧
        c - b n < 1 / ((n : ℝ) + 1)) ∧
      (∀ (n : ℕ),
        HasDerivWithinAt
          (fun y : ℝ => if y ≤ b n then w y else w (b n) + (y - b n))
          (deriv w (b n)) (Iic (b n)) (b n) ∧
        HasDerivWithinAt
          (fun y : ℝ => if y ≤ b n then w y else w (b n) + (y - b n))
          1 (Ici (b n)) (b n) ∧
        1 - deriv w (b n) ≤ 0) ∧
      ∀ (n : ℕ) (y : ℝ), 0 ≤ y →
        0 ≤ (if y ≤ c then w y else w c + (y - c)) -
          (if y ≤ b n then w y else w (b n) + (y - b n)) ∧
        (if y ≤ c then w y else w c + (y - c)) -
          (if y ≤ b n then w y else w (b n) + (y - b n)) <
          1 / ((n : ℝ) + 1) := by sorry
