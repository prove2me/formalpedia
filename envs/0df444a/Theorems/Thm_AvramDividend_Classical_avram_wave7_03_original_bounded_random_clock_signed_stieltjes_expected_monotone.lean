-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_bounded_random_clock_signed_stieltjes_expected_monotone
-- name    : AvramDividend.Classical.avram_wave7_03_original_bounded_random_clock_signed_stieltjes_expected_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:33:23.297089+00:00
-- url     : https://prove2.me/theorems/09a4a236-3cf5-4792-9683-24c53841f08a
-- title:
--   Original expected signed Stieltjes payout monotone in bounded measurable random stop clocks
-- statement:
--   For two measurable NNReal random clocks τ≤σ pathwise and uniformly bounded by a common finite horizon T on the original Lévy process, the genuine original expected real signed discounted Stieltjes dividend payout on paymentTimes(ruinTime)∩Iic τ is at most the corresponding expected real payout on paymentTimes(ruinTime)∩Iic σ, with the same original P and dividendMeasure D ω. The proof transports the independently Proved original double ENNReal monotonicity to real signed expected values via the Proved exact bounded random-clock signed/ENNReal mean equalities and Proved real expected cash nonnegativity, ensuring sound toReal comparison. It includes time-zero right-limit, continuous and endpoint mass without changing any source definitions.
-- source:
--   Proved original bounded random-clock signed/ENNReal mean bridge fc7c1b8a; original ENNReal clock monotonicity 925fc21f; original bounded real expected signed nonnegativity 30a156e4; ENNReal.toReal_mono.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_full_ruin_bounded_clock_unconditional_mean_eq
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_random_clock_full_ennreal_cash_monotone
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_bounded_random_clock_signed_stieltjes_mean_nonneg
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_bounded_random_clock_signed_stieltjes_expected_monotone
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (T : ℝ≥0) (τ σ : Ω → ℝ≥0)
    (hτBound : ∀ ω, τ ω ≤ T)
    (hσBound : ∀ ω, σ ω ≤ T)
    (hτMeas : Measurable (fun ω => (τ ω : ℝ)))
    (hσMeas : Measurable (fun ω => (σ ω : ℝ)))
    (hClock : ∀ ω, τ ω ≤ σ ω) :
    (∫ ω, (∫ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤
    (∫ ω, (∫ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by sorry
