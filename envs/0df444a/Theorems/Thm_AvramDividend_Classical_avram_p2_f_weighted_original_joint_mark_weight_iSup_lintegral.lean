-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_joint_mark_weight_iSup_lintegral
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_joint_mark_weight_iSup_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:29:41.058802+00:00
-- url     : https://prove2.me/theorems/bcd8b124-4e9a-413d-9a44-50647ece9a6e
-- title:
--   Joint weight-and-mark monotone convergence for the original Lévy jump count
-- statement:
--   For the genuine original Lévy intrinsic marked jump measure, simultaneous increasing measurable path weights and increasing Borel jump-mark sets commute with the nonnegative expectation and diagonal supremum. Handles infinite weights and jump counts including zero-times-infinity. Uses a separate proved ENNReal directed-product lemma; identifies no ν-rate.
-- source:
--   Original-path mark continuity from below, intrinsic rectangle measurability, ENNReal diagonal iSup product lemma, Mathlib lintegral_iSup.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_rectangle_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_monotone_mark_pathwise

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_joint_mark_weight_iSup_lintegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (B : ℕ → Set ℝ)
    (hB : ∀ n, MeasurableSet (B n))
    (hBMono : Monotone B)
    (H : ℕ → Ω → ℝ≥0∞)
    (hH : ∀ n, Measurable (H n))
    (hHMono : ∀ i j, i ≤ j → ∀ ω, H i ω ≤ H j ω) :
    (∫⁻ ω, (⨆ n, H n ω) * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ (⋃ n, B n)) ∂P) =
    ⨆ n, (∫⁻ ω, H n ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ (B n)) ∂P) := by sorry
