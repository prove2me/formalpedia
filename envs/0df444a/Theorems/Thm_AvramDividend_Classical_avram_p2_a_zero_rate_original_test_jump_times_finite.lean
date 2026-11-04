-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_test_jump_times_finite
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_original_test_jump_times_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:13:48.36834+00:00
-- url     : https://prove2.me/theorems/12fc4493-1858-4533-94f4-03d4e6e44abb
-- title:
--   Original source compact-negative continuous test jumps have finite support per finite horizon
-- statement:
--   For the exact original Lévy sample path, a real test vanishing for all jump marks within ε of zero can be nonzero at only finitely many actual jump times on (0,T]. Obtain this finite support directly from the already Proved pathwise finite δ-jump theorem, with no expected rate, Poisson model or compensator.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_finite_horizon_separated_jump_marks_finite_every_path

open MeasureTheory Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_original_test_jump_times_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (T : ℝ≥0) (ε : ℝ) (hε : 0 < ε)
    (f : ℝ → ℝ) (hf : ∀ y : ℝ, dist y 0 < ε → f y = 0) :
    {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
      f (X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) ≠ 0}.Finite := by sorry
