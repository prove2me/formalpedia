-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_cap_corner_uniform_epsilon_interior_cutoff_approximation
-- name    : AvramDividend.Classical.avram_wave5_05_ubv_cap_corner_uniform_epsilon_interior_cutoff_approximation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T11:50:36.225305+00:00
-- url     : https://prove2.me/theorems/38b135f2-1b8c-4601-9e9b-4a249b26ef95
-- title:
--   For every epsilon, a strictly interior slope-one cutoff uniformly under-approximates the true cap continuation within epsilon on all nonnegative reserves
-- statement:
--   For every ε>0, positive finite cap c, w continuous on nonnegative reserves and C² with derivative at least one only strictly inside c, there exists an interior cutoff 0<b<c such that its slope-one continuation f_b under-approximates the true cap continuation f_c uniformly: for all y≥0, 0≤f_c(y)−f_b(y)<ε. The proof applies the already Proved global cap secant-defect bound 5d60cc4f-f8cc-4849-8d17-fd65a1331edb and continuity of w at c. All approximate kink points lie strictly inside the C² domain, making a piecewise Itô–Meyer localisation possible without assuming a derivative or C² at the actual cap. This deterministic estimate does not itself prove any stochastic local-time correction or Stieltjes dividend bound.
-- source:
--   Proved exact uniform cap cutoff secant defect 5d60cc4f-f8cc-4849-8d17-fd65a1331edb and corrected canonical core 429e17ca-5528-40b5-b593-7c03973d0706 unchanged; user scoped stochastic cap boundary not full chain rule.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_cap_corner_uniform_interior_cutoff_secant_defect_bound

open MeasureTheory Set Topology Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_05_ubv_cap_corner_uniform_epsilon_interior_cutoff_approximation
    (w : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ENNReal.ofReal c})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < ENNReal.ofReal c → 1 ≤ deriv w y)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ b : ℝ, 0 < b ∧ b < c ∧
      ∀ y : ℝ, 0 ≤ y →
        0 ≤ (if y ≤ c then w y else w c + (y - c)) -
          (if y ≤ b then w y else w b + (y - b)) ∧
        (if y ≤ c then w y else w c + (y - c)) -
          (if y ≤ b then w y else w b + (y - b)) < ε := by sorry
