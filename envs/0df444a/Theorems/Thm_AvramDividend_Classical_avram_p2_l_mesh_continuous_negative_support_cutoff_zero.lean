-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_continuous_negative_support_cutoff_zero
-- name    : AvramDividend.Classical.avram_p2_l_mesh_continuous_negative_support_cutoff_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T09:39:30.190567+00:00
-- url     : https://prove2.me/theorems/6361cb43-abd7-449e-8f59-3ceba49a0bfd
-- title:
--   Continuity enforces zero at the negative test support cutoff
-- statement:
--   A real continuous marked test that is identically zero strictly to the right of -rho is also zero at -rho. This supplies the endpoint lemma needed for uniform interval-step approximation even in the presence of cutoff jump atoms.

import Mathlib

open Set Topology

theorem AvramDividend.Classical.avram_p2_l_mesh_continuous_negative_support_cutoff_zero (f : ℝ → ℝ) (ρ : ℝ) (hfcont : Continuous f) (hf : ∀ z : ℝ, -ρ < z → f z = 0) : f (-ρ) = 0 := by sorry
