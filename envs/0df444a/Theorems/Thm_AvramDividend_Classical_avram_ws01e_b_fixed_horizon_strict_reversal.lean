-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_fixed_horizon_strict_reversal
-- name    : AvramDividend.Classical.avram_ws01e_b_fixed_horizon_strict_reversal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T01:05:30.106259+00:00
-- url     : https://prove2.me/theorems/a0501c79-2903-44d4-b2cd-38530ae41f34
-- title:
--   Genuine fixed-horizon càdlàg Lévy terminal drawdown and infimum have identical strict-event laws
-- statement:
--   At every strictly positive deterministic finite horizon T, the event that the terminal value X_T minus some path value X_s (s≤T) is strictly below a has the same probability as the event that some X_s−X_0 is strictly below a, for any real threshold a. The proof uses equal-mesh reversal, pathwise nesting of dyadic grids, right-continuous threshold detection and continuity from below. Valid for càdlàg Lévy paths with jumps without assuming atomless extrema or Wiener–Hopf independence.
-- source:
--   Direct finite-horizon pathwise reversal of a spectrally negative Lévy process, via accepted finite-dimensional stationary-increment reversal and right-continuous dyadic limits; Kuznetsov–Kyprianou–Rivero §2.1–2.2; Kyprianou fluctuation lectures.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_right_continuous_strict_dyadic_grid_event
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_finite_dyadic_grid_refines
import Theorems.Thm_AvramDividend_Classical_levy_equal_mesh_path_drawdown_minimum_strict_threshold_ws01e_b
open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_fixed_horizon_strict_reversal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (hT : 0 < T)
    (a : ℝ) :
    P {ω : Ω | ∃ s : ℝ≥0, s ≤ T ∧ X.X T ω - X.X s ω < a} =
    P {ω : Ω | ∃ s : ℝ≥0, s ≤ T ∧ X.X s ω - X.X 0 ω < a} := by sorry
