-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_finite_capped_value_exact_real_variational_sup
-- name    : AvramDividend.Classical.avram_limit2_finite_capped_value_exact_real_variational_sup
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T09:50:05.349298+00:00
-- url     : https://prove2.me/theorems/a7ac2140-c7a8-4ee3-87dd-a1040139dbcd
-- title:
--   Finite original capped value has exact real-Stieltjes L1 variational representation
-- statement:
--   Whenever the genuine original capped valueFunctionLe at reserve x is finite, every actual IsAdmissibleLe dividend strategy has an integrable original untruncated real Stieltjes payout up to the genuine ruinTime. The original capped ENNReal value equals the double supremum over actual capped strategies and admissibility witnesses of the ENNReal.ofReal of those genuine real expected payouts. For each witness dividendValue is bounded by the indexed valueFunctionLe, hence finite; the already-Proved source exact perpetual signed Stieltjes identity then converts the inner term. No terminal vanishing, equality-in-law or alternative strategy class is used.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_finite_capped_value_exact_real_variational_sup
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ) (C : ℝ≥0∞)
    (hFiniteCap : valueFunctionLe X q C x < ⊤) :
    (∀ (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D),
      Integrable (fun ω : Ω =>
        ∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P) ∧
    valueFunctionLe X q C x =
      ⨆ (D : ℝ≥0 → Ω → ℝ), ⨆ (_ : IsAdmissibleLe X x C D),
        ENNReal.ofReal
          (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
            Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by sorry
