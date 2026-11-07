-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f4_turn17_positive_ray_growth
-- name    : AvramDividend.Classical.avram_p4_f4_turn17_positive_ray_growth
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T12:20:50.500005+00:00
-- url     : https://prove2.me/theorems/4170b742-d0d8-4e41-92bc-7b9ca9d7aab9
-- title:
--   Factorised ODE upper envelope on the ray y≥1
-- statement:
--   The original factorised second-order inequality controls the positive ray from basepoint one; eliminates all boundary and negative-half-line glue.
-- source:
--   Source-exact mathematical reduction of f8c60858; independent positive ray, initial compact interval and global glue.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f4_turn17_positive_ray_growth
    (rpos rneg : ℝ) (hrpos : 0 < rpos) (hrneg : rneg < 0)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTop : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hODE : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      iteratedDeriv 2 w y - (rpos + rneg) * deriv w y + rpos * rneg * w y ≤ 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ, 1 ≤ y →
      w y ≤ K * Real.exp (rpos * y) := by sorry
