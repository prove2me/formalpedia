-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn10_original_unit_shortcell_power
-- name    : AvramDividend.Classical.avram_bv_jump8_turn10_original_unit_shortcell_power
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:37:07.920186+00:00
-- url     : https://prove2.me/theorems/83a5577d-7cdb-4923-93fd-ac98f8c8c09e
-- title:
--   Original-X marked finite-product unit expectation equals the power of equal short cells
-- statement:
--   For the actual stationary independent increment Lévy process, split the literal original (0,1] strict negative marked product into n+1 disjoint equally spaced intervals, derive independence and stationarity of the finite marked product weights, and obtain the n+1 power of the original (0,1/(n+1)] product expectation.
-- source:
--   For the actual stationary independent increment Lévy process, split the literal original (0,1] strict negative marked product into n+1 disjoint equally spaced intervals, derive independence and stationarity of the finite marked product weights, and obtain the n+1 power of the original (0,1/(n+1)] product expectation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_jump8_turn10_original_unit_shortcell_power
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (k n : ℕ) :
    let T : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
    (∫ ω : Ω, ∏ u ∈
        (avram_redux19_original_strict_negative_marked_times_finite X ω (1 : ℝ≥0) k).toFinset,
        Real.exp (X.X u ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u) ∂P) = (∫ ω : Ω, ∏ u ∈
        (avram_redux19_original_strict_negative_marked_times_finite X ω T k).toFinset,
        Real.exp (X.X u ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u) ∂P) ^ (n + 1) := by sorry
