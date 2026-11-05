-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_continuous_negative_test_global_right_tail
-- name    : AvramDividend.Classical.avram_p2_l_mesh_continuous_negative_test_global_right_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T11:04:23.304463+00:00
-- url     : https://prove2.me/theorems/3eeff26a-2733-44fe-b30a-8bf9a63fe783
-- title:
--   Globally small right tail of a continuous negative-supported jump test
-- statement:
--   A real marked test that vanishes strictly to the right of -ρ and is continuous at -ρ has, for every positive η, a cut B strictly below -ρ such that |f(z)|≤η for every z>B, including points beyond the nominal support cutoff. This provides the complete exterior right-tail estimate for the uniform interval-step approximation without excluding a mark at -ρ.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_continuous_test_small_left_cutoff_strip

open AvramDividend.Classical

theorem AvramDividend.Classical.avram_p2_l_mesh_continuous_negative_test_global_right_tail
    (f : ℝ → ℝ) (ρ η : ℝ) (hη : 0 < η)
    (hfcont : ContinuousAt f (-ρ)) (hfzero : f (-ρ) = 0)
    (hf : ∀ z : ℝ, -ρ < z → f z = 0) :
    ∃ B : ℝ, B < -ρ ∧ ∀ z : ℝ, B < z → |f z| ≤ η := by sorry
