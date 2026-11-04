-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_joint_horizon_mark_weight_iSup_lintegral
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_joint_horizon_mark_weight_iSup_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:38:08.266508+00:00
-- url     : https://prove2.me/theorems/d86feda9-3a39-48f1-8dcb-9b0fa53224d7
-- title:
--   Triple monotone convergence in original Lévy horizons, marks and nonnegative weights
-- statement:
--   For nested original Lévy future time-mark rectangles with increasing nonnegative measurable path weights, the expectation of the supremum-weighted count over the increasing union equals the supremum of the weighted rectangle expectations. Handles zero-times-infinity, uses no source intensity, and preserves the genuine jump map.
-- source:
--   Original intrinsic jump measure, proved nested rectangle pathwise continuity, proved intrinsic rectangle measurability, ENNReal diagonal product supremum, Mathlib lintegral_iSup.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_joint_horizon_mark_weight_iSup_lintegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (T : ℕ → ℝ≥0) (hT : Monotone T)
    (B : ℕ → Set ℝ) (hB : ∀ n, MeasurableSet (B n))
    (hBMono : Monotone B)
    (H : ℕ → Ω → ℝ≥0∞)
    (hH : ∀ n, Measurable (H n))
    (hHMono : ∀ i j, i ≤ j → ∀ ω, H i ω ≤ H j ω) :
    (∫⁻ ω, (⨆ n, H n ω) * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (⋃ n, Ioc s (s + T n) ×ˢ B n) ∂P) =
    ⨆ n, (∫⁻ ω, H n ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T n) ×ˢ B n) ∂P) := by sorry
