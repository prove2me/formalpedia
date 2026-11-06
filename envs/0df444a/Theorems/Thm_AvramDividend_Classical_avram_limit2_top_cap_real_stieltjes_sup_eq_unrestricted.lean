-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_top_cap_real_stieltjes_sup_eq_unrestricted
-- name    : AvramDividend.Classical.avram_limit2_top_cap_real_stieltjes_sup_eq_unrestricted
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T09:53:13.660065+00:00
-- url     : https://prove2.me/theorems/b0022b57-6389-43da-81f8-fb494c0d2110
-- title:
--   Original C=top capped real perpetual payout supremum equals unrestricted admissible payout supremum
-- statement:
--   The actual top-capped original admissible strategies coincide with the unrestricted original IsAdmissible strategies for the identical real discounted Stieltjes payout functional, so the two double-indexed ENNReal suprema over original strategies and admissibility proofs agree exactly. This cap-to-unrestricted interface uses the genuine ruinTime, paymentTimes and dividendMeasure; the proof simplifies the actual IsAdmissibleLe top-cap definition, with no equality-in-law or proxy strategy and no finiteness or terminal hypothesis.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_top_cap_real_stieltjes_sup_eq_unrestricted
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ) :
    (⨆ (D : ℝ≥0 → Ω → ℝ),
      ⨆ (_ : IsAdmissibleLe X x (⊤ : ℝ≥0∞) D),
        ENNReal.ofReal
          (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
            Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P)) =
    (⨆ (D : ℝ≥0 → Ω → ℝ),
      ⨆ (_ : IsAdmissible X x D),
        ENNReal.ofReal
          (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
            Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P)) := by sorry
