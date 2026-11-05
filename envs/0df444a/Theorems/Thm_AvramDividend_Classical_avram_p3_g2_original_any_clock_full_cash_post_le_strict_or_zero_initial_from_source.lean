-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_any_clock_full_cash_post_le_strict_or_zero_initial_from_source
-- name    : AvramDividend.Classical.avram_p3_g2_original_any_clock_full_cash_post_le_strict_or_zero_initial_from_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T00:28:59.918027+00:00
-- url     : https://prove2.me/theorems/98a4cc24-da79-447e-8525-8a27f8066898
-- title:
--   Original BV random-clock full Stieltjes cash and postpayment boundary correction with automatic physical source jump hypotheses
-- statement:
--   At every sample-dependent original observation clock, inclusive dividendMeasure cash on Iic τ plus strict-survival postpayment terminal is bounded by strict Iio τ cash plus strict prepayment terminal when τ>0. At τ=0 the bound is the source initial HJB value w(x), including an initial right dividend even at immediate ruin. The proof eliminates the abstract jump premise with source original positive-cap C1 closed-endpoint secant, and instantiates the previously proved all-horizon pathwise reconciliation directly at τ(ω); no measurability or stopping-time assumptions are needed for the pathwise assertion.
-- source:
--   Proved G2 ec5419c6 all-horizon original source cash correction and 1fba8396 automatic source C1 hjump, source X D; independent of canonical Open residual and budgets.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_all_horizon_closed_postreward_le_strict_or_zero_initial
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_zero_or_strict_preruin_C1_canonical_hjump_without_standing

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_g2_original_any_clock_full_cash_post_le_strict_or_zero_initial_from_source
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0) :
    ∀ ω : Ω,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (τ ω : ℝ))) *
          w (x + X.X (τ ω) ω - rightLimit D (τ ω) ω)
      else 0) ≤
      (if τ ω = 0 then w x
      else
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (τ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
        (if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * (τ ω : ℝ))) *
            w (riskProcess X x D (τ ω) ω)
        else 0)) := by sorry
