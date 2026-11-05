-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_compact_test_uniform_modulus
-- name    : AvramDividend.Classical.avram_p2_l_mesh_compact_test_uniform_modulus
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T09:46:05.614237+00:00
-- url     : https://prove2.me/theorems/d8dfe33e-849d-42d0-866a-23eec788a2aa
-- title:
--   Uniform modulus for a compactly supported original marked test
-- statement:
--   Every real continuous compactly supported marked test has a single positive real delta for each positive eta such that all real points less than delta apart have test values less than eta apart. The uniform global bound is needed to control all finite uniform-grid partition cells in the independent step-density proof.

import Mathlib

open Topology

theorem AvramDividend.Classical.avram_p2_l_mesh_compact_test_uniform_modulus (f : ℝ → ℝ) (hfcomp : HasCompactSupport f) (hfcont : Continuous f) (η : ℝ) (hη : 0 < η) : ∃ δ : ℝ, 0 < δ ∧ ∀ x y : ℝ, |x - y| < δ → |f x - f y| < η := by sorry
