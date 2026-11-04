-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_weight_sup_lintegral_eq_iSup
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_weight_sup_lintegral_eq_iSup
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T16:51:31.206573+00:00
-- url     : https://prove2.me/theorems/6d2af5cf-4b7b-495a-8bc0-7a0d955ec27b
-- title:
--   Original jump-count weighted monotone convergence from sup of past weights
-- statement:
--   For an increasing sequence of measurable nonnegative weights, the expected genuine original intrinsic marked Lévy count multiplied by their pointwise supremum equals the supremum of the weighted expectations. ENNReal.iSup_mul handles 0 times infinity exactly, and Mathlib monotone convergence handles all nonnegative values, with no original jump-rate assumption.
-- source:
--   Pinned Mathlib ENNReal.iSup_mul, MeasureTheory.lintegral_iSup; Proved intrinsic original rectangle measurable d9c55240.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_rectangle_measurable

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_weight_sup_lintegral_eq_iSup
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (H : ℕ → Ω → ℝ≥0∞) (hMeas : ∀ n, Measurable (H n))
    (hMono : Monotone H) :
    (∫⁻ ω, (⨆ n : ℕ, H n ω) * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B) ∂P) =
    ⨆ n : ℕ, (∫⁻ ω, H n ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B) ∂P) := by sorry
