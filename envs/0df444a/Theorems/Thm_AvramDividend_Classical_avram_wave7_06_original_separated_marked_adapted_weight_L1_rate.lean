-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_separated_marked_adapted_weight_L1_rate
-- name    : AvramDividend.Classical.avram_wave7_06_original_separated_marked_adapted_weight_L1_rate
-- status  : Open
-- author  : @WillR
-- created : 2026-11-03T07:07:01.633785+00:00
-- url     : https://prove2.me/theorems/d27347c9-2df4-4de8-b038-5bce4c50d754
-- title:
--   Exact original Lévy marked-cell L¹ compensation against arbitrary adapted ENNReal weights
-- statement:
--   For any nonnegative original-past measurable weight H, any Borel negative mark set separated from zero, and arbitrary deterministic future time rectangle, the true original Lévy marked jump count weighted by H has expected rate E[H] T ν(B). No bounded-variation assumption or auxiliary Poisson model. The only outstanding imported mathematics is zero-origin ν intensity and source marked time stationarity.
-- source:
--   Original stopped predictability L1 compensation needed by W7-07 and W7-08, built from Proved original future path-factorisation and exact Open P2 rate/stationarity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_separated_marked_adapted_weight_L1_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (H : Ω → ℝ≥0∞)
    (hH : Measurable[𝓕 s] H)
    (B : Set ℝ) (hB : MeasurableSet B)
    (ε : ℝ) (hε : 0 < ε) (hBsep : B ⊆ Iic (-ε)) :
    (∫⁻ ω, H ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B) ∂P) =
      (∫⁻ ω, H ω ∂P) * ((T : ℝ≥0∞) * X.ν B) := by sorry
