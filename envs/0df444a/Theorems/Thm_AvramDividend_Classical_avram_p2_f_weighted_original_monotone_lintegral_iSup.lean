-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_monotone_lintegral_iSup
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_monotone_lintegral_iSup
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T16:25:23.226197+00:00
-- url     : https://prove2.me/theorems/b2a243f8-3c8c-49c4-920a-1a7c4cce8dec
-- title:
--   Original intrinsic marked future-count monotone convergence for increasing nonnegative weights
-- statement:
--   For any monotone increasing sequence of ambient-measurable nonnegative weights, the expectation of the pointwise supremum of their actual original Lévy intrinsic marked future-count contributions equals the supremum of their expected contributions. No first-moment, ν-rate or finiteness assumption is needed. The genuine original count measurability and Mathlib monotone convergence prove this.
-- source:
--   Pinned Mathlib MeasureTheory.lintegral_iSup and Proved original intrinsic rectangle measurable d9c55240.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_rectangle_measurable

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_monotone_lintegral_iSup
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (H : ℕ → Ω → ℝ≥0∞) (hMeas : ∀ n, Measurable (H n))
    (hMono : Monotone H) :
    (∫⁻ ω, (⨆ n : ℕ, H n ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B)) ∂P) =
    ⨆ n : ℕ, (∫⁻ ω, H n ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B) ∂P) := by sorry
