-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_BV_bounded_random_clock_signed_post_le_pre_expected
-- name    : AvramDividend.Classical.avram_p3_g2_original_BV_bounded_random_clock_signed_post_le_pre_expected
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T00:32:41.570709+00:00
-- url     : https://prove2.me/theorems/1a4e3d68-1792-47a7-8c13-bab615aa47be
-- title:
--   True original BV stopped terminal expected postpayment is bounded by prepayment for any bounded measurable random clock
-- statement:
--   For the original bounded-variation spectrally negative Lévy process, original capped admissible strategy and an arbitrary bounded measurable physical random clock, prove that the true signed strict-survival discounted postpayment and prepayment terminal rewards are both integrable and that expected postpayment ≤ expected prepayment. The proof imports independent real signed postpayment L1, new source prepayment random-clock L1 (including joint original reserve measurability), and source-exact all-clock closed-cap jump comparison. The same ruin-survival event occurs in both terms, excluding the terminal at a ruin tie and respecting the time-zero right atom.
-- source:
--   Original source X, D; G2 signed post L1 10c9f283, source random pre L1 pending, all-clock physical prepost pathwise 5c31e329 publication pending. No open canonical P3 lemma or equality-in-law.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_bounded_random_clock_signed_postterminal_L1
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_BV_bounded_random_clock_strict_prepayment_terminal_L1
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_any_clock_strict_postpayment_terminal_le_prepayment

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_g2_original_BV_bounded_random_clock_signed_post_le_pre_expected
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_meas : Measurable w)
    (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 < q)
    (H : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτMeas : Measurable τ) (hτBound : ∀ ω, τ ω ≤ H) :
    let Post : Ω → ℝ := fun ω =>
      if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (τ ω : ℝ))) *
          w (x + X.X (τ ω) ω - rightLimit D (τ ω) ω)
      else 0
    let Pre : Ω → ℝ := fun ω =>
      if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (τ ω : ℝ))) *
          w (riskProcess X x D (τ ω) ω)
      else 0
    Integrable Post P ∧ Integrable Pre P ∧
      (∫ ω, Post ω ∂P) ≤ (∫ ω, Pre ω ∂P) := by sorry
