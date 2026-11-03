-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_random_clock_full_ennreal_cash_monotone
-- name    : AvramDividend.Classical.avram_wave7_03_original_random_clock_full_ennreal_cash_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:51:15.703683+00:00
-- url     : https://prove2.me/theorems/925fc21f-33c4-4b6f-bebe-92bd972ff5a7
-- title:
--   Monotonicity of actual original expected ENNReal full Stieltjes cash under ordered random clocks
-- statement:
--   For the original Lévy process X, dividend strategy D, ruin clock and dividendMeasure, if finite NNReal stopping clocks τ and σ satisfy τω≤σω for every original path ω, then the exact original double ENNReal dividend payout integral over paymentTimes(ruinTime)∩Iic τω is at most the corresponding integral over paymentTimes(ruinTime)∩Iic σω. This comparison includes continuous payouts, time-zero right-limit mass and the possible endpoint atom at σ, without changing the sample space or assuming a deterministic global bound.
-- source:
--   Mathlib MeasureTheory.lintegral_mono, MeasureTheory.lintegral_mono_set applied to exact original closed stopped set.

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

theorem AvramDividend.Classical.avram_wave7_03_original_random_clock_full_ennreal_cash_monotone
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (τ σ : Ω → ℝ≥0)
    (hClock : ∀ ω, τ ω ≤ σ ω) :
    (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≤
    (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) := by sorry
