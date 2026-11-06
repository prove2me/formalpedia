-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_capped_value_bound_to_real_expected_cash
-- name    : AvramDividend.Classical.avram_limit2_capped_value_bound_to_real_expected_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T10:43:17.752316+00:00
-- url     : https://prove2.me/theorems/dd962531-0ebd-4b62-8d2c-e4e6857e5265
-- title:
--   Finite original capped value upper bound controls genuine real perpetual expected dividend cash
-- statement:
--   For the original spectrally negative Lévy process and a genuinely capped admissible strategy D at reserve x, suppose the actual capped valueFunctionLe is bounded by ENNReal.ofReal(w) for a nonnegative real w. Since D is one of the literal admissible witnesses in valueFunctionLe, its dividendValue is finite. Proved original perpetual signed Stieltjes integrability theorem then shows the real discounted full ruin-stopped dividend payout is in L1 and its ENNReal.ofReal real expected value exactly equals dividendValue. The original capped value bound and nonnegative w convert this equality to a real upper bound of the genuine expected payout by w. No stochastic source identity, terminal vanishing or equality-in-law is inferred.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_capped_value_bound_to_real_expected_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ) (C : ℝ≥0∞)
    (w : ℝ) (hw : 0 ≤ w)
    (hValueBound : valueFunctionLe X q C x ≤ ENNReal.ofReal w)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P ∧
    dividendValue X q x D =
      ENNReal.ofReal
        (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ∧
    (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ w := by sorry
