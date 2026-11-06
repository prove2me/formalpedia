-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_original_signed_strict_fatou_real_grid_certificate
-- name    : AvramDividend.Classical.avram_limit2_original_signed_strict_fatou_real_grid_certificate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T13:10:09.657873+00:00
-- url     : https://prove2.me/theorems/25d406ec-9af9-4242-a8c0-13809875d62c
-- title:
--   Actual original signed strict stopped cash plus pre-rightpayment terminal Fatou lower-limit expected bound
-- statement:
--   This lemma matches the new original BV signed stochastic grid certificate's exact liminf expression: ENNReal.ofReal of original stopped strict Iio T cash.toReal plus the signed real pre-rightpayment surviving terminal, rather than a fabricated nonnegative terminal or a closed cutoff. Given genuine measurable nonnegative ENNReal F_n with uniformly bounded expectations and an AE lower-liminf certificate for that exact expression, pinned Mathlib's Fatou inequality produces the expected upper bound of its ofReal positive part. No cash finiteness, terminal nonnegativity or terminal vanishing is silently assumed; further signed real-value conversion remains a separate obligation.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_original_signed_strict_fatou_real_grid_certificate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (Term : Ω → ℝ)
    (F : ℕ → Ω → ℝ≥0∞) (B : ℝ≥0∞)
    (hFmeas : ∀ n, Measurable (F n))
    (hMean : ∀ n, (∫⁻ ω, F n ω ∂P) ≤ B)
    (hFatou : ∀ᵐ ω ∂P,
      ENNReal.ofReal
        (((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)).toReal) + Term ω) ≤
        liminf (fun n : ℕ => F n ω) atTop) :
    (∫⁻ ω, ENNReal.ofReal
      (((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal) + Term ω) ∂P) ≤ B := by sorry
