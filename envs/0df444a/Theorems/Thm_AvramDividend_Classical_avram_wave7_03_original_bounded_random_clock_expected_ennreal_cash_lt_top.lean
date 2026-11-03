-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_bounded_random_clock_expected_ennreal_cash_lt_top
-- name    : AvramDividend.Classical.avram_wave7_03_original_bounded_random_clock_expected_ennreal_cash_lt_top
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:35:51.335792+00:00
-- url     : https://prove2.me/theorems/a0a9a75e-b98c-4dc9-8590-7d52ac57edc0
-- title:
--   Finite expected original full ruin-stopped ENNReal dividends at any bounded measurable random clock
-- statement:
--   For the original Levy process and cap-admissible dividend strategy, the full expected double ENNReal Stieltjes payout over paymentTimes(ruinTime X x D ω)∩Iic(τ ω) against exactly dividendMeasure D ω and P is finite for every bounded measurable NNReal random clock, q>=0. The proof uses the Proved unconditional same-measure random-clock equality to express it as ENNReal.ofReal of a genuine real signed Stieltjes expectation and applies ENNReal.ofReal_lt_top. Preserves right-limit time-zero atom, diffuse/interior jump payments and strict positive ruin exclusion.
-- source:
--   Proved W7-03 original full ruin bounded clock unconditional expected real/ENNReal equality fc7c1b8a and ENNReal.ofReal_lt_top.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_full_ruin_bounded_clock_unconditional_mean_eq
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_bounded_random_clock_expected_ennreal_cash_lt_top
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτBound : ∀ ω, τ ω ≤ T)
    (hτMeas : Measurable (fun ω => (τ ω : ℝ))) :
    (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) < ⊤ := by sorry
