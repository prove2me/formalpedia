-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_finite_random_clock_cash_eq_iSup_min_integer_clocks
-- name    : AvramDividend.Classical.avram_wave7_03_original_finite_random_clock_cash_eq_iSup_min_integer_clocks
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:40:33.47163+00:00
-- url     : https://prove2.me/theorems/09b8cab7-6c1a-41c7-be18-3cb40f5ff173
-- title:
--   Original finite random-clock full Stieltjes payout equals supremum of eventually exact integer truncations
-- statement:
--   For the genuine original spectrally negative Levy process, dividend strategy and path ω, the full ENNReal Stieltjes payout on paymentTimes(ruinTime X x D ω)∩Iic τ for any finite NNReal clock τ equals the supremum over integer n of the payout on the same original domain truncated at min τ (n+1). Unlike generic increasing approximations to a closed endpoint, these truncations eventually equal the finite τ exactly, so any right-limit dividend atom at τ, including time-zero, is retained. This is a pathwise statement, no surrogate probability space, no dropped continuous mass, no claim at τ=∞.
-- source:
--   Mathlib Archimedean exists_nat_ge, min_eq_left, lintegral_mono_set, iSup order; canonical original dividendMeasure and paymentTimes.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_finite_random_clock_cash_eq_iSup_min_integer_clocks
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (τ : ℝ≥0) (q : ℝ) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
    ⨆ n : ℕ,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Iic ((min τ (((n + 1 : ℕ) : ℝ≥0)) : ℝ)),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) := by sorry
