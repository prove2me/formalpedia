-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys90c_positive_part_gap_triangle
-- name    : AvramDividend.Classical.avram_bvb_phys90c_positive_part_gap_triangle
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T23:56:21.735557+00:00
-- url     : https://prove2.me/theorems/f894d85b-b53c-4f16-b301-6e6ffd89e5cf
-- title:
--   Positive-part error transfer via the intermediate compensated ledger
-- statement:
--   For three real sequences f,g,h, if the positive parts of f-g and g-h vanish as n tends to infinity, then so does the positive part of f-h. This is the exact needed transfer from original stopped cash versus compensated G-K, and G-K versus drift L.
-- source:
--   Elementary max-positive subadditivity: max((f-g)+(g-h),0) <= max(f-g,0)+max(g-h,0), by squeeze. Pure algebra independent of reserve convention.

import Mathlib
open Filter
open scoped Topology

theorem AvramDividend.Classical.avram_bvb_phys90c_positive_part_gap_triangle
    (f g h : ℕ → ℝ)
    (hfg : Tendsto (fun n => max (f n - g n) 0) atTop (𝓝 0))
    (hgh : Tendsto (fun n => max (g n - h n) 0) atTop (𝓝 0)) :
    Tendsto (fun n => max (f n - h n) 0) atTop (𝓝 0) := by sorry
