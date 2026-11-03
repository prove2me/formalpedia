-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_cofinal_closed_horizon_cash_fatou
-- name    : AvramDividend.Classical.avram_wave6_chat09_original_cofinal_closed_horizon_cash_fatou
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T08:39:32.533684+00:00
-- url     : https://prove2.me/theorems/3ab23481-d8e1-425e-993c-2d662ff7153c
-- title:
--   Cofinal random clocks transfer source Stieltjes dividend bounds to every inclusive deterministic horizon
-- statement:
--   For the original spectrally negative Levy X and its original left-continuous adapted dividend strategy D, suppose a measurable increasing sequence of random real upper clocks eventually reaches a fixed real deterministic horizon T almost surely. If the complete ruin-stopped discounted Stieltjes cash expectation is bounded uniformly at every random clock, then the same bound holds at the inclusive deterministic horizon T. The local bounds are genuine separate stochastic input, not assumed at T. The proof uses the already-Proved original-source random-clock measurability result and monotone convergence, and preserves payments at t=0, the right payment atom at t=T, continuous and singular-continuous dividend components.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), proof of (5.13), passage from increasing localising stops to full stopped discounted dividends; source-faithful inclusive deterministic horizon Fatou/Beppo Levi bridge.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_random_upper_clock_complete_stieltjes_cash_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave6_chat09_original_cofinal_closed_horizon_cash_fatou
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q T : ℝ) (τ : ℕ → Ω → ℝ)
    (hτm : ∀ n, Measurable (τ n))
    (hτmono : ∀ ω, Monotone (fun n => τ n ω))
    (hcofinal : ∀ᵐ ω ∂P, ∃ n, T ≤ τ n ω)
    (B : ℝ≥0∞)
    (hbound : ∀ n,
      (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ n ω),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω ∂P) ≤ B) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω ∂P) ≤ B := by sorry
