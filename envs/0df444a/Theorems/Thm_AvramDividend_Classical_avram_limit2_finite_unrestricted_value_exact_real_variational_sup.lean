-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_finite_unrestricted_value_exact_real_variational_sup
-- name    : AvramDividend.Classical.avram_limit2_finite_unrestricted_value_exact_real_variational_sup
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T09:50:13.260299+00:00
-- url     : https://prove2.me/theorems/d492bd00-e114-4b6b-b04d-153ab7be44af
-- title:
--   Finite original unrestricted value is exact supremum of real integrable perpetual dividend payouts
-- statement:
--   If the original unrestricted valueFunction is finite at the real reserve x, then every genuinely original IsAdmissible dividend strategy has an L1 real full-ruin-time Stieltjes discounted dividend payout, and the original valueFunction is exactly the supremum over all original admissible strategies and their admissibility witnesses of the ENNReal.ofReal real expected payout. Each strategy dividendValue is below the actual indexed unrestricted valueFunction, and the accepted finite original perpetual signed Stieltjes theorem proves its real integrability and expected-value identity. Two congruences on the original double indexed supremum establish the exact variational formula without equality-in-law or terminal vanishing.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_finite_unrestricted_value_exact_real_variational_sup
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (hFiniteValue : valueFunction X q x < ⊤) :
    (∀ (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D),
      Integrable (fun ω : Ω =>
        ∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P) ∧
    valueFunction X q x =
      ⨆ (D : ℝ≥0 → Ω → ℝ), ⨆ (_ : IsAdmissible X x D),
        ENNReal.ofReal
          (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
            Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by sorry
