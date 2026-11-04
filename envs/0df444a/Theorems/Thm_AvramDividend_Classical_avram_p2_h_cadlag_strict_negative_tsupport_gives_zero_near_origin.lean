-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_strict_negative_tsupport_gives_zero_near_origin
-- name    : AvramDividend.Classical.avram_p2_h_cadlag_strict_negative_tsupport_gives_zero_near_origin
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T19:45:12.439408+00:00
-- url     : https://prove2.me/theorems/bae46d34-f927-4de0-8ea3-0652d7db96f6
-- title:
--   A strictly negative closed test support has a neighbourhood of zero where the test vanishes
-- statement:
--   For a real test function with its closed topological support entirely strictly negative, give an explicit positive radius around zero on which the function vanishes; use closed support and metric neighbourhood separation.

import Mathlib

namespace AvramDividend.Classical
end AvramDividend.Classical

open Set Filter Topology

theorem AvramDividend.Classical.avram_p2_h_cadlag_strict_negative_tsupport_gives_zero_near_origin (f : ℝ → ℝ)
    (hneg : tsupport f ⊆ Set.Iio (0 : ℝ)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ z : ℝ, |z| < ρ → f z = 0 := by sorry
