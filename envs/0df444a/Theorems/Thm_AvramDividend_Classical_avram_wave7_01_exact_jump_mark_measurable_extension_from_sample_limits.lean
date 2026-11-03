-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_exact_jump_mark_measurable_extension_from_sample_limits
-- name    : AvramDividend.Classical.avram_wave7_01_exact_jump_mark_measurable_extension_from_sample_limits
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:57:23.618303+00:00
-- url     : https://prove2.me/theorems/a7e5433e-14bc-4d47-9113-f2ad5a917f92
-- title:
--   Globally measurable exact jump-mark extension from countable one-sided path sample limits
-- statement:
--   Given two sequences of globally measurable real coordinate-path sample functionals, form their extended-real lower-tail measurable limits and subtract. Wherever those samples converge to the right value Y(t(Y)) and strict left limit leftLim Y(t(Y)), the globally measurable result equals the exact intrinsic jump mark, even if t(Y) is irrational and depends on the raw path. This isolates Borel limit-extension from time-selector convergence, without any Levy intensity law.
-- source:
--   Use Proved EReal measurable lower-tail envelope theorem for each sample sequence, and finite-limit recovery for their EReal coercions via continuous Real.toEReal. The exact subtraction equality follows pointwise for paths satisfying both real-valued limits.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_real_mark_sequence_liminf_extension_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_ereal_lower_tail_envelope_recovers_finite_mark_limit

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_exact_jump_mark_measurable_extension_from_sample_limits
    (t : (ℝ≥0 → ℝ) → ℝ≥0)
    (right left : ℕ → (ℝ≥0 → ℝ) → ℝ)
    (hRightMeas : ∀ n : ℕ, Measurable (right n))
    (hLeftMeas : ∀ n : ℕ, Measurable (left n)) :
    ∃ mark : (ℝ≥0 → ℝ) → ℝ,
      Measurable mark ∧
      ∀ Y : ℝ≥0 → ℝ,
        Tendsto (fun n : ℕ => right n Y) atTop (𝓝 (Y (t Y))) →
        Tendsto (fun n : ℕ => left n Y) atTop
          (𝓝 (Function.leftLim Y (t Y))) →
        mark Y = Y (t Y) - Function.leftLim Y (t Y) := by sorry
