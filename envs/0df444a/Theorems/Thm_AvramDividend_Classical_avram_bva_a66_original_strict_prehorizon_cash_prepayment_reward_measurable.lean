-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a66_original_strict_prehorizon_cash_prepayment_reward_measurable
-- name    : AvramDividend.Classical.avram_bva_a66_original_strict_prehorizon_cash_prepayment_reward_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T00:05:04.738576+00:00
-- url     : https://prove2.me/theorems/606bc7b2-4d25-400d-aa50-0b4cee8d9137
-- title:
--   Measurability of original actual stopped strict cash and true prepayment surviving terminal at any nonnegative horizon
-- statement:
--   The original actual strict-before-r dividend Stieltjes cash plus killed terminal pre-right-dividend candidate value, embedded in ENNReal, is a measurable random variable for each nonnegative deterministic r. This is an original-source technical ingredient for the A63 correct prepayment terminal Fatou bridge, without infinite-activity compensation assumptions, and uses the separately Proved original strict-cash measurability, adapted riskProcess and ruinTime events.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_a66_original_strict_prehorizon_cash_prepayment_reward_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (r : ℝ≥0) :
    Measurable (fun ω : Ω => ENNReal.ofReal
      ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (r : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal +
       (if (r : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * (r : ℝ))) * w (riskProcess X x D r ω)
        else 0))) := by sorry
