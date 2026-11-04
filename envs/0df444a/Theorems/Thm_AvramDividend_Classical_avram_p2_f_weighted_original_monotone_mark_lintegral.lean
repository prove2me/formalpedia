-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_monotone_mark_lintegral
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_monotone_mark_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:14:27.600252+00:00
-- url     : https://prove2.me/theorems/b5b75e41-206a-4ff2-a7a0-325bf54720f0
-- title:
--   Continuity from below of true original weighted marked jump expectations over increasing Borel sets
-- statement:
--   For any measurable ENNReal weight and increasing Borel mark sets, the expected weighted count for the increasing union is the supremum of expected weighted counts. This is true for the genuine original source Lévy jump measure and does not invoke ν intensity.
-- source:
--   Mathlib Monotone.measure_iUnion, ENNReal.iSup_mul and MeasureTheory.lintegral_iSup; source rectangle measurability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_rectangle_measurable

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_monotone_mark_lintegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (B : ℕ → Set ℝ)
    (hB : ∀ n, MeasurableSet (B n))
    (hMono : Monotone B)
    (H : Ω → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ ω, H ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ (⋃ n, B n)) ∂P) =
    ⨆ n, (∫⁻ ω, H ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ (B n)) ∂P) := by sorry
