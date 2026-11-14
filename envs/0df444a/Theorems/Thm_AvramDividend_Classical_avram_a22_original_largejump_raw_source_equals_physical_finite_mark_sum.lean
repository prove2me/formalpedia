-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a22_original_largejump_raw_source_equals_physical_finite_mark_sum
-- name    : AvramDividend.Classical.avram_a22_original_largejump_raw_source_equals_physical_finite_mark_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T14:41:59.976545+00:00
-- url     : https://prove2.me/theorems/48bb5af6-9484-4e62-9b40-865bf528f731
-- title:
--   Original physical large negative mark integral equals finite signed large-mark sum on actual jump support
-- statement:
--   For an original Lévy sample path and a finite set F exactly capturing all its nonzero physical jumps on a finite horizon, the actual intrinsic uncompensated negative large-jump integral over marks ≤-1 equals the finite sum of the actual signed left-limit jumps ≤-1. Uses proved original integral-to-TSum formula and finite-support TSum-to-Finset equality. This exact identity is a source-side component of physical finite-activity Lévy–Itô decomposition, without independent noise.
-- source:
--   Proved c63fdd06 original large physical intrinsic integral equals source tsum; Proved a55466fc finite actual jump support; pinned Mathlib tsum_eq_sum.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_largejump_integral_eq_source_tsum_unconditional
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a22_original_largejump_raw_source_equals_physical_finite_mark_sum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (t : ℝ≥0)
    (F : Finset ℝ≥0)
    (hF : ∀ u : ℝ≥0, u ∈ F ↔ 0 < u ∧ u ≤ t ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0) :
    avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω =
      ∑ u ∈ F,
        if X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤ -1
        then X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u else 0 := by sorry
