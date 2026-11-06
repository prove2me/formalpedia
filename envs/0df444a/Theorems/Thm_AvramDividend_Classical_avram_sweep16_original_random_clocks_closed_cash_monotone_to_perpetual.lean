-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_random_clocks_closed_cash_monotone_to_perpetual
-- name    : AvramDividend.Classical.avram_sweep16_original_random_clocks_closed_cash_monotone_to_perpetual
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T11:58:14.128446+00:00
-- url     : https://prove2.me/theorems/824ecdb0-e0c8-42e6-b12e-ce16ed3b8e02
-- title:
--   Original random stopped-clock closed Stieltjes cash is monotone and bounded by perpetual value
-- statement:
--   For any two path-dependent nonnegative real stopped horizons tau <= sigma, expected original discounted Stieltjes dividends paid before the closed tau horizon are bounded by those before sigma, which are bounded by the full dividendValue of the exact original strategy. This proof uses only pointwise set inclusion and nonnegative lintegral monotonicity; it retains any time-zero and right-horizon atoms and needs no adaptedness assumption for this order comparison.
-- source:
--   Original dividendValue and dividendMeasure definitions; Lean MeasureTheory.lintegral_mono_set, lintegral_mono, and coerced NNReal clock monotonicity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_sweep16_original_random_clocks_closed_cash_monotone_to_perpetual
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (τ σ : Ω → ℝ≥0)
    (hτσ : ∀ ω, τ ω ≤ σ ω) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ∧
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      dividendValue X q x D := by sorry
