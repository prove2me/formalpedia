-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a26_original_finite_activity_no_tiny_marks_eventually_20261114
-- name    : AvramDividend.Classical.avram_a26_original_finite_activity_no_tiny_marks_eventually_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T00:31:50.311438+00:00
-- url     : https://prove2.me/theorems/766fcf43-3207-4503-a544-da823aa37469
-- title:
--   Original finite-activity source eventually has no physical negative marks in any omitted shrinking cutoff band on a compact horizon
-- statement:
--   On one source conull event, for any fixed finite physical horizon all sufficiently small omitted negative-jump cutoff bands contain no actual original Levy jumps uniformly across the horizon.
-- source:
--   A26 original physical negative mark margin and pinned Mathlib tendsto_one_div_add_atTop_nhds_zero_nat.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- For each compact source horizon, all sufficiently fine negative-jump omitted cutoff bands contain no physical marks. -/

theorem AvramDividend.Classical.avram_a26_original_finite_activity_no_tiny_marks_eventually_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∃ N : ℕ, ∀ n ≥ N, ∀ u : ℝ≥0,
      0 < u → u ≤ T →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
        ∉ Ioo (-(1 / ((n : ℝ) + 1))) 0 := by sorry
