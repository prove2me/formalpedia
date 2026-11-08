-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn10_original_shortcell_product_quadratic
-- name    : AvramDividend.Classical.avram_bv_jump8_turn10_original_shortcell_product_quadratic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:37:14.88042+00:00
-- url     : https://prove2.me/theorems/3e7158b4-5dd2-43bd-b957-0f557b7ab7d8
-- title:
--   Original-X strict negative marked product short-cell first-order collision error
-- statement:
--   For the actual original X negative marked finite product over the short interval 1/(n+1), the first-order expansion has expectation 1 - (1/(n+1)) times the exact Lévy mark loss 1-exp(y), with a nonnegative error at most ν(Iic(-δ))²/(n+1)². Reuse source-exact marked Campbell identity db9a5093, product collision bound 9cf0f7c2, second moment cd66a508, and strict-to-closed finite cardinal bridge.
-- source:
--   For the actual original X negative marked finite product over the short interval 1/(n+1), the first-order expansion has expectation 1 - (1/(n+1)) times the exact Lévy mark loss 1-exp(y), with a nonnegative error at most ν(Iic(-δ))²/(n+1)². Reuse source-exact marked Campbell identity db9a5093, product collision bound 9cf0f7c2, second moment cd66a508, and strict-to-closed finite cardinal bridge.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_jump8_turn10_original_shortcell_product_quadratic
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (k n : ℕ) :
    let T : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
    let q : ℝ := (∫ ω : Ω, ∏ u ∈
        (avram_redux19_original_strict_negative_marked_times_finite X ω T k).toFinset,
        Real.exp (X.X u ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u) ∂P)
    let a : ℝ := (∫ y in Iio (-(1 / ((k : ℝ) + 1))), (1 - Real.exp y) ∂X.ν)
    let C : ℝ := (X.ν (Iic (-(1 / ((k : ℝ) + 1))))).toReal ^ 2
    0 ≤ q ∧ q ≤ 1 ∧
    0 ≤ q - (1 - a / ((n + 1 : ℕ) : ℝ)) ∧
    q - (1 - a / ((n + 1 : ℕ) : ℝ)) ≤
      C / ((n + 1 : ℕ) : ℝ) ^ 2 := by sorry
