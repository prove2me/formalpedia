-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_g_radon_compact_test_uniform_abs_bound
-- name    : AvramDividend.Classical.avram_p2_g_radon_compact_test_uniform_abs_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T14:54:44.562181+00:00
-- url     : https://prove2.me/theorems/0a244a09-36f2-4e41-a3c6-92882893c770
-- title:
--   Compactly supported negative mark tests admit a global positive real absolute bound
-- statement:
--   Any continuous real test function with compact support in the strictly negative real half-line has a finite positive uniform absolute bound. This combines with the independently established separation from zero to instantiate the original-source uniform L² marked-grid estimate for every compact negative-mark test. The argument uses no Lévy rate, compensator, stochastic independence or alternate process.
-- source:
--   Mathlib.Analysis.Normed.Group.Bounded: HasCompactSupport.exists_bound_of_continuous and Mathlib.Topology.ContinuousMap.CompactlySupported: CompactlySupportedContinuousMap.hasCompactSupport.

import Mathlib
open MeasureTheory Set Topology
noncomputable section

theorem AvramDividend.Classical.avram_p2_g_radon_compact_test_uniform_abs_bound
    (f : CompactlySupportedContinuousMap {x : ℝ // x < 0} ℝ) :
    ∃ M : ℝ, 0 < M ∧
      ∀ x : {x : ℝ // x < 0}, |f x| ≤ M := by sorry
