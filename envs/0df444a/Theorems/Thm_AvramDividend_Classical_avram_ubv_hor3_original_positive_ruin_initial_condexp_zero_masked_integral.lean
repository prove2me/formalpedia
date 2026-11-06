-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_positive_ruin_initial_condexp_zero_masked_integral
-- name    : AvramDividend.Classical.avram_ubv_hor3_original_positive_ruin_initial_condexp_zero_masked_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:29:17.664447+00:00
-- url     : https://prove2.me/theorems/e8169f69-9568-4521-a282-5ba151337010
-- title:
--   Original positive-ruin event annihilates initial-conditionally centred physical martingale terminal integrals
-- statement:
--   For the actual original Lévy process X, its right-continuous filtration and an admissible dividend strategy D, any integrable real source terminal M whose conditional expectation given the initial right-continuous sigma-algebra is zero has zero real expectation when masked to the strictly positive ruin-time event. Uses the previously Proved initial-event measurability theorem and pinned Mathlib conditional expectation on a measurable set. This is the exact missing bridge for event-localised source centring; the physical condexp-zero premise is explicit and remains to be established for each stochastic component.
-- source:
--   Uses original zero-ruin initial-event measurable theorem 165b6853, X.isProbability and pinned MeasureTheory.setIntegral_condExp, ae_restrict_of_ae. No synthetic Poisson process, equality-in-law or assertion of the physical conditional martingale property.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_zero_ruin_event_rightcont_initial_measurable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_hor3_original_positive_ruin_initial_condexp_zero_masked_integral
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (M : Ω → ℝ) (hMI : Integrable M P)
    (hCondZero : ∀ᵐ ω ∂P,
      condExp (𝓕.rightCont 0) P M ω = 0) :
    (∫ ω in {ω : Ω | ruinTime X x D ω ≠ 0}, M ω ∂P) = 0 := by sorry
