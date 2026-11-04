-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_g_radon_compact_test_separated_from_zero
-- name    : AvramDividend.Classical.avram_p2_g_radon_compact_test_separated_from_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T14:51:39.652198+00:00
-- url     : https://prove2.me/theorems/21cfff7d-78c6-466e-9e2b-6f7b1901dbb7
-- title:
--   Every compactly supported continuous negative-mark test vanishes on a band next to zero
-- statement:
--   For a compactly supported continuous real test function defined on the strictly negative real marks, there is a positive epsilon such that the function vanishes on the entire negative band (-epsilon,0). This deterministic topological separation supplies the exact negative mark support bound required for source-specific uniform L² grid controls. It assumes no Lévy rate, jump compensator or path law.
-- source:
--   Mathlib.Topology.ContinuousMap.CompactlySupported: hasCompactSupport; Mathlib.Topology.Order.Compact: IsCompact.exists_isMaxOn; Mathlib.Topology.Algebra.Support: subset_tsupport.

import Mathlib
open MeasureTheory Set Topology
noncomputable section

theorem AvramDividend.Classical.avram_p2_g_radon_compact_test_separated_from_zero
    (f : CompactlySupportedContinuousMap {x : ℝ // x < 0} ℝ) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ x : {x : ℝ // x < 0}, -ε < (x : ℝ) → f x = 0 := by sorry
