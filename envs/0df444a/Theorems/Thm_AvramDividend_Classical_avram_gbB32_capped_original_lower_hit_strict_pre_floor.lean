-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB32_capped_original_lower_hit_strict_pre_floor
-- name    : AvramDividend.Classical.avram_gbB32_capped_original_lower_hit_strict_pre_floor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T19:08:09.242341+00:00
-- url     : https://prove2.me/theorems/bcfd8832-5710-4c55-8c2d-472b6145a1cd
-- title:
--   Original capped first lower hit guarantees strict reserve floor before stopping
-- statement:
--   For any real-valued process U, any upper horizon H and lower threshold b, show that strictly before the first time U≤b capped by H, U must lie strictly above b. This is a pure exact source-order argument, requiring no sample continuity or measurability, and gives the strict pre-floor hFloor obligation needed by Gaussian physical-grid stopped cash.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB32_capped_original_lower_hit_strict_pre_floor
    {Ω : Type*} (U : ℝ≥0 → Ω → ℝ)
    (H : ℝ≥0) (b : ℝ) (ω : Ω) (t : ℝ≥0)
    (ht : t < sInf ((Icc (0 : ℝ≥0) H ∩
      (fun u : ℝ≥0 => -(U u ω)) ⁻¹' Ici (-b)) ∪ {H})) :
    b < U t ω := by sorry
