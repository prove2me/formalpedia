-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_zero_discount_value_eq_full_preruin_stieltjes_mass
-- name    : AvramDividend.Classical.avram_wave7_03_original_zero_discount_value_eq_full_preruin_stieltjes_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:18:50.558627+00:00
-- url     : https://prove2.me/theorems/af9bfa81-73c8-4700-b67d-2695b29c092a
-- title:
--   Zero-discount original dividendValue is exactly expected full strict pre-ruin Stieltjes payment mass
-- statement:
--   At zero discount the canonical original complete dividendValue is precisely the expected source dividendMeasure mass of paymentTimes(ruinTime) on the same Ω and P, including the time-zero right-limit atom and every continuous and jump dividend strictly before positive ruin. This is an exact ENNReal identity valid for infinite values without a finiteness or integrability assumption, and identifies the undiscounted upper bound in the rate-monotonicity bridge with the actual q=0 expected original dividend value.
-- source:
--   Canonical source dividendValue and discounted integral at q=0; Real.exp_zero, ENNReal.ofReal_one, Mathlib lintegral_one and source paymentTimes/dividendMeasure.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_zero_discount_value_eq_full_preruin_stieltjes_mass
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) :
    dividendValue X 0 x D =
      (∫⁻ ω : Ω,
        (dividendMeasure D ω) (paymentTimes (ruinTime X x D ω)) ∂P) := by sorry
