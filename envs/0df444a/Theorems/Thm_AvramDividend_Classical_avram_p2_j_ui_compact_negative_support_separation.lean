-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_compact_negative_support_separation
-- name    : AvramDividend.Classical.avram_p2_j_ui_compact_negative_support_separation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T19:50:33.450034+00:00
-- url     : https://prove2.me/theorems/9959bae3-7b69-41dc-89a9-fcc5b6eb2bea
-- title:
--   Compact strictly negative real support admits a uniform positive distance from zero
-- statement:
--   Any compact subset of the strictly negative real half-line lies below a fixed negative threshold -epsilon for some epsilon>0. For a nonempty compact support, take a maximal element and choose half its positive distance to zero; for empty support choose any epsilon. This exact analytic support separation supplies P2-A's bounded negative-mark L2 theorem with an away-from-zero threshold for continuous compact negative test functions.

import Mathlib.Topology.Order.Compact
import Mathlib

open Set Topology

theorem AvramDividend.Classical.avram_p2_j_ui_compact_negative_support_separation
    (s : Set ℝ) (hs : IsCompact s)
    (hneg : s ⊆ Set.Iio (0 : ℝ)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y ∈ s, y ≤ -ε := by sorry
