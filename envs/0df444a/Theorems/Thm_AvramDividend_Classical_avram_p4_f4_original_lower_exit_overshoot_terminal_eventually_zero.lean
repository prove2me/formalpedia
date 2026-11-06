-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f4_original_lower_exit_overshoot_terminal_eventually_zero
-- name    : AvramDividend.Classical.avram_p4_f4_original_lower_exit_overshoot_terminal_eventually_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:22:36.432143+00:00
-- url     : https://prove2.me/theorems/9d18b870-2705-41e5-a900-a114df2cc45f
-- title:
--   Original lower-exit negative-overshoot stopped terminal is eventually exactly zero almost surely
-- statement:
--   For the actual source X and D with the precise stopped post-rightpayment reserve W_k, an almost-sure eventually positive stopping clock at or after ruin and strictly negative actual riskProcess reserve forces the associated discounted terminal Term_k to be identically zero on the tail. It identifies the negative-overshoot branch separately from the nonzero creeping w(0) branch, and does not assume the actual overshoot event holds without proof.
-- source:
--   Use ruinTime ≤ positive stop to select the original ruin branch of W_k; apply zero extension w(y)=0 for negative riskProcess to the exact discounted Term_k.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f4_original_lower_exit_overshoot_terminal_eventually_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (hw_neg : ∀ y < 0, w y = 0)
    (τk : ℕ → Ω → ℝ≥0)
    (Wk Termk : ℕ → Ω → ℝ)
    (hWk : ∀ k ω, Wk k ω =
      if τk k ω = 0 ∨ (τk k ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τk k ω) ω - rightLimit D (τk k ω) ω
      else riskProcess X x D (τk k ω) ω)
    (hTermk : ∀ k ω, Termk k ω =
      Real.exp (-(q * (τk k ω : ℝ))) * w (Wk k ω))
    (hovershoot : ∀ᵐ ω ∂P, ∀ᶠ k in atTop,
      0 < τk k ω ∧
      ruinTime X x D ω ≤ (τk k ω : ℝ≥0∞) ∧
      riskProcess X x D (τk k ω) ω < 0) :
    ∀ᵐ ω ∂P, ∀ᶠ k in atTop, Termk k ω = 0 := by sorry
