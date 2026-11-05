-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_continuous_test_small_left_cutoff_strip
-- name    : AvramDividend.Classical.avram_p2_l_mesh_continuous_test_small_left_cutoff_strip
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T09:41:50.30013+00:00
-- url     : https://prove2.me/theorems/d93f1377-b931-41ca-9af7-ff6e949fc77f
-- title:
--   Small left cutoff strip for continuous compact test approximation
-- statement:
--   If a real marked test is continuous at its negative cutoff and zero at that cutoff, then it is uniformly arbitrarily small in a sufficiently short interval just to the left. This permits choosing a final interval-step endpoint strictly below the cutoff, including when a jump mark is exactly at the cutoff.

import Mathlib

open Topology

theorem AvramDividend.Classical.avram_p2_l_mesh_continuous_test_small_left_cutoff_strip (f : ℝ → ℝ) (ρ ε : ℝ) (hε : 0 < ε) (hfcont : ContinuousAt f (-ρ)) (hfzero : f (-ρ) = 0) : ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℝ, -ρ - δ < z → z ≤ -ρ → |f z| < ε := by sorry
