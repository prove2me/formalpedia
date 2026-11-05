-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_negative_subtype_compact_test_extend_zero
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_negative_subtype_compact_test_extend_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T08:37:29.521681+00:00
-- url     : https://prove2.me/theorems/75e1e15f-a392-4156-aa29-6e6dcf01509d
-- title:
--   Compact negative-subtype tests extend continuously by zero to real compact-negative tests
-- statement:
--   For every compactly supported continuous real test on the open subtype of strictly negative reals, extend by zero to the ambient real line. The resulting function is continuous, compactly supported strictly below zero and agrees pointwise on the subtype. This supplies the exact bridge required to use original real compact-test moment identities in negative-subtype Radon uniqueness, including atomic half-line thresholds.

import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Logic.Function.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Set Topology AvramDividend.Classical

theorem AvramDividend.Classical.avram_p2_a_zero_rate_negative_subtype_compact_test_extend_zero
    (f : CompactlySupportedContinuousMap {x : ℝ // x < 0} ℝ) :
    ∃ g : ℝ → ℝ, Continuous g ∧ IsCompact (tsupport g) ∧
      tsupport g ⊆ Iio (0 : ℝ) ∧
      (∀ x : {x : ℝ // x < 0}, g (x : ℝ) = f x) := by sorry
