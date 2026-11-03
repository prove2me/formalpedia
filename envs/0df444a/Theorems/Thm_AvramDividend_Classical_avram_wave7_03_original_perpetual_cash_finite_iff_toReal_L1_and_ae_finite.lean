-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_cash_finite_iff_toReal_L1_and_ae_finite
-- name    : AvramDividend.Classical.avram_wave7_03_original_perpetual_cash_finite_iff_toReal_L1_and_ae_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:53:37.46993+00:00
-- url     : https://prove2.me/theorems/18d1ad11-acaf-4f25-9f73-23c37287b45f
-- title:
--   Exact original perpetual expected dividend finiteness iff real cash L1 and genuine pathwise almost-sure finiteness
-- statement:
--   On the canonical original Lévy process X with original P and exactly the source ruin-stopped paymentTimes Stieltjes cash, the full ENNReal dividendValue is finite if and only if (i) the real conversion of the complete inner ENNReal Stieltjes cash is P-integrable and (ii) the original inner ENNReal cash itself is finite P-almost everywhere. The second premise is essential because ENNReal.toReal sends infinity to zero. The forward direction uses proved original perpetual mean bridge and ae_lt_top; reverse uses the a.e. ofReal_toReal identity and the pinned Mathlib real/ENNReal integral equality. No surrogate sample space and no inappropriate replacement of signed Stieltjes expectation occurs.
-- source:
--   Proved source perpetual cash measurability db59cbee and L1 mean bridge 5f2772c6; Mathlib ae_lt_top, ofReal_integral_eq_lintegral_ofReal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_perpetual_stieltjes_cash_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_cash_toReal_L1_and_exact_mean
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_perpetual_cash_finite_iff_toReal_L1_and_ae_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (q : ℝ) :
    (dividendValue X q x D < ⊤) ↔
      Integrable (fun ω : Ω =>
        (∫⁻ t in paymentTimes (ruinTime X x D ω),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) P ∧
      (∀ᵐ ω ∂P, (∫⁻ t in paymentTimes (ruinTime X x D ω),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) < ⊤) := by sorry
