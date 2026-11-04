-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_g_radon_compact_test_zero_extension_continuous_and_compact
-- name    : AvramDividend.Classical.avram_p2_g_radon_compact_test_zero_extension_continuous_and_compact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T14:58:35.890089+00:00
-- url     : https://prove2.me/theorems/c4fbc606-9358-47a0-9a95-8216b853d6ba
-- title:
--   Extension by zero of compactly supported negative-mark tests is continuous and compactly supported on real marks
-- statement:
--   A continuous compactly supported real test function on the open negative real half-line extends by zero through Subtype.val to a continuous compactly supported function on all real marks. This is the deterministic source-faithful bridge between negative-mark compact test integrals and test functions evaluated at actual real Lévy increments, without any jump rate, extra filtration, coupling or compensator assumption.
-- source:
--   Mathlib.Topology.Algebra.Support: HasCompactSupport.continuous_extend_zero, HasCompactSupport.extend_zero; open set Iio 0 with Subtype.val.

import Mathlib
open MeasureTheory Set Topology
noncomputable section

theorem AvramDividend.Classical.avram_p2_g_radon_compact_test_zero_extension_continuous_and_compact
    (f : CompactlySupportedContinuousMap {x : ℝ // x < 0} ℝ) :
    Continuous (Function.extend (Subtype.val : {x : ℝ // x < 0} → ℝ) (fun x => f x) 0) ∧
    HasCompactSupport (Function.extend (Subtype.val : {x : ℝ // x < 0} → ℝ) (fun x => f x) 0) := by sorry
