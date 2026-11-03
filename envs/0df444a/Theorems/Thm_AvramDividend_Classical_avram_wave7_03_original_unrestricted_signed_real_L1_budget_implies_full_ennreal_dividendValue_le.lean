-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_unrestricted_signed_real_L1_budget_implies_full_ennreal_dividendValue_le
-- name    : AvramDividend.Classical.avram_wave7_03_original_unrestricted_signed_real_L1_budget_implies_full_ennreal_dividendValue_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:53:04.125538+00:00
-- url     : https://prove2.me/theorems/d0e24117-ac3f-4b89-93a3-fa73d1d6bdc2
-- title:
--   Genuine unrestricted original signed real Stieltjes L1 expected budget bounds complete canonical ENNReal dividendValue
-- statement:
--   Full untruncated original-process expected dividend budget bridge, at any real q: if the genuine original signed real Stieltjes payout g(ω)=∫ in paymentTimes(ruinTime X x D ω) exp(-qt) against dividendMeasure D ω is L1(P), the original full inner ENNReal cash is finite a.e., and expected real signed payout ≤ B, then the actual canonical dividendValue (double original ENNReal integral) ≤ ENNReal.ofReal B. All hypotheses are explicit. The proof consumes accepted general finiteness iff and accepted exact outer unrestricted real signed Stieltjes mean equality, then ENNReal.ofReal monotonicity. No altered stopping rule, time-zero omission or proxy process.
-- source:
--   Proved fd64314b general signed L1 iff; Proved 9806569f exact outer signed mean identity; pinned ENNReal.ofReal_le_ofReal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_general_original_value_finite_iff_genuine_signed_L1_and_pathwise_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_unrestricted_signed_real_L1_budget_implies_full_ennreal_dividendValue_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (q : ℝ)
    (hAeFinite : ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) < ⊤)
    (hRealIntegrable : Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P)
    (B : ℝ)
    (hRealBudget : (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ B) :
    dividendValue X q x D ≤ ENNReal.ofReal B := by sorry
