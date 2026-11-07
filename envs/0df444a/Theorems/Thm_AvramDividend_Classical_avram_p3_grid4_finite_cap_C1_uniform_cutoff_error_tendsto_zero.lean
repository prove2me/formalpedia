-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_finite_cap_C1_uniform_cutoff_error_tendsto_zero
-- name    : AvramDividend.Classical.avram_p3_grid4_finite_cap_C1_uniform_cutoff_error_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T10:02:02.498051+00:00
-- url     : https://prove2.me/theorems/91cb2e34-e788-4988-954d-9b927c344a83
-- title:
--   C1 finite-cap linear-cutoff source error vanishes uniformly along arbitrary nonnegative reserve sequences
-- statement:
--   Given an actual finite dividend cap C>0, the canonical BV C1 interior gradient bound and continuity of w on nonnegative reserves, choose any interior cutoff b_n between zero and C converging to C. For any sequence of nonnegative original reserve states y_n, potentially hitting or crossing C, the difference between the full cap-linear continuation and the cutoff's own slope-one continuation converges to zero, uniformly controlled by the deterministic scalar cap secant defect. This eliminates a spurious cap-derivative-equals-one assumption in the separate physical-grid approximation step.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_finite_cap_C1_uniform_cutoff_defect_bound
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_finite_cap_corner_scalar_defect_tendsto_zero
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_finite_cap_C1_uniform_cutoff_error_tendsto_zero
    (C : ℝ≥0∞) (hC : 0 < C) (hfinite : C ≠ ⊤)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (b y : ℕ → ℝ) (hb0 : ∀ n, 0 ≤ b n)
    (hbC : ∀ n, b n ≤ C.toReal)
    (hb : Tendsto b atTop (𝓝 C.toReal))
    (hy : ∀ n, 0 ≤ y n) :
    Tendsto (fun n => (if y n ≤ C.toReal then w (y n)
      else w C.toReal + (y n - C.toReal)) -
      (if y n ≤ b n then w (y n)
       else w (b n) + (y n - b n)))
      atTop (𝓝 (0 : ℝ)) := by sorry
