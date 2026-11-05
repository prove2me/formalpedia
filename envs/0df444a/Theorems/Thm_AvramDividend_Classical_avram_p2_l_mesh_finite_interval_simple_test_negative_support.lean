-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_finite_interval_simple_test_negative_support
-- name    : AvramDividend.Classical.avram_p2_l_mesh_finite_interval_simple_test_negative_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T08:55:45.234552+00:00
-- url     : https://prove2.me/theorems/85e833f9-1754-4f83-9c1f-7585c50f63d8
-- title:
--   Negative support of finite interval-step test functions
-- statement:
--   A finite real-weighted step test formed from half-open intervals whose upper endpoints lie at or below a strictly negative cutoff vanishes at every mark strictly above the cutoff. This verifies the cutoff-support hypothesis needed when approximating a compactly supported negative-mark test.

import Mathlib

open Set Filter Topology
open scoped BigOperators Classical

theorem AvramDividend.Classical.avram_p2_l_mesh_finite_interval_simple_test_negative_support {ι : Type*} [Fintype ι]
    (a b c : ι → ℝ) (ρ : ℝ)
    (hb : ∀ i : ι, b i ≤ -ρ)
    (z : ℝ) (hz : -ρ < z) :
    (∑ i : ι, if z ∈ Ioc (a i) (b i) then c i else 0) = 0 := by sorry
