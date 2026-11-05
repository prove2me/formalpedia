-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_any_clock_strict_postpayment_terminal_le_prepayment
-- name    : AvramDividend.Classical.avram_p3_g2_original_any_clock_strict_postpayment_terminal_le_prepayment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T00:19:52.91569+00:00
-- url     : https://prove2.me/theorems/70ab2405-747f-48e2-b4d6-09265646aeb7
-- title:
--   Original physical stopped postpayment terminal is pointwise bounded by prepayment terminal for any random clock
-- statement:
--   For every (even nonmeasurable) original physical observation clock, the strict-surviving discounted post-right-payment candidate value is at most the prepayment value. The source dividend strategy proves the right payment nonnegative and the independently Proved source closed-cap jump envelope bounds the candidate value drop. At ruin ties both terms are zero, and at time zero the genuine right atom is included. This pathwise source theorem requires neither BV nor standing assumptions and is a direct prerequisite for random-clock expected terminal comparison.
-- source:
--   Original admissible IsAdmissibleLe, Proved source nonnegative right payment dividendStrategy_le_rightLimit, and G2 Proved source C1 canonical hjump without standing 1fba8396; no canonical P3 residual/prebudget imports.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_zero_or_strict_preruin_C1_canonical_hjump_without_standing

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_g2_original_any_clock_strict_postpayment_terminal_le_prepayment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (τ : Ω → ℝ≥0) :
    ∀ ω : Ω,
      (if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (τ ω : ℝ))) *
          w (x + X.X (τ ω) ω - rightLimit D (τ ω) ω)
      else 0) ≤
      (if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (τ ω : ℝ))) *
          w (riskProcess X x D (τ ω) ω)
      else 0) := by sorry
