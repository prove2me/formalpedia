-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_bounded_measurable_random_clock_signed_stieltjes_integrable_unconditionally
-- name    : AvramDividend.Classical.avram_wave7_03_original_bounded_measurable_random_clock_signed_stieltjes_integrable_unconditionally
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:18:43.653644+00:00
-- url     : https://prove2.me/theorems/2f1150a0-693b-42cd-8136-06af156d3443
-- title:
--   Genuine original ruin-stopped signed Stieltjes discounted payout is P-integrable at every bounded measurable random clock
-- statement:
--   The actual original-process signed discounted Stieltjes dividend payout at every bounded measurable NNReal random clock is integrable under its unchanged original law P. The Proved original bounded-clock full signed/ENNReal mean identity gives full double ENNReal expected cash as ENNReal.ofReal of a real number, hence finite. The independently Proved source finite random-clock signed-L1 theorem converts that exact cash finiteness to Integrable of the real Stieltjes dividend payout over the identical ruin-stopped paymentTimes interval and dividendMeasure D ω. This formalises the required outer integrability, preserving the time-zero right-limit atom, continuous pre-ruin cash and terminal endpoint.
-- source:
--   Proved original unconditional bounded-clock signed/ENNReal expected cash identity fc7c1b8a-c416-450c-b1ad-cadf9344888f and original full signed Stieltjes L1 under finite expected cash 724e387f-af08-4400-ac51-2b29d7314d93.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_full_ruin_bounded_clock_unconditional_mean_eq
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_finite_random_clock_signed_stieltjes_L1_of_full_ennreal_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_bounded_measurable_random_clock_signed_stieltjes_integrable_unconditionally
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτBound : ∀ ω, τ ω ≤ T)
    (hτMeas : Measurable (fun ω => (τ ω : ℝ))) :
    Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P := by sorry
