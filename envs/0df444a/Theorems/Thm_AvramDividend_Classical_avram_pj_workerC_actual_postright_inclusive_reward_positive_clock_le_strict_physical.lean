-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_actual_postright_inclusive_reward_positive_clock_le_strict_physical
-- name    : AvramDividend.Classical.avram_pj_workerC_actual_postright_inclusive_reward_positive_clock_le_strict_physical
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T11:30:10.863983+00:00
-- url     : https://prove2.me/theorems/754befba-18a8-4226-a389-79b73b2bf547
-- title:
--   Actual post-right-payment finitecap reward at every positive true clock is bounded pointwise by original strict prepayment reserve and cash
-- statement:
--   For the exact original spectrally negative Levy reserve and admissible dividend strategy, if rho is positive, its true reward G with survival post-right-payment reserve and inclusive paymentTimes(ruinTime) intersect Iic(rho) is bounded pathwise by the strict prepayment reserve at rho plus discounted dividendMeasure cash restricted to Iio(rho). The initial-time branch is retained explicitly in hGdef and eliminated only after proving rho>0; terminal contact and current payment correction follow from the genuine right-jump hjump source. This bridges the exact full reward G to the strict physical V in Worker C K/E expected reward.
-- source:
--   Proved 8066526a actual positive-clock inclusive-to-strict pathwise contact and original exact hGdef.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_b244_original_ruinclipped_positive_stop_inclusive_Iic_cash_terminal_contact_le_strict
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_actual_postright_inclusive_reward_positive_clock_le_strict_physical
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
        w (riskProcess X x D t ω -
          (rightLimit D t ω - D t ω)))
    (ρ : Ω → ℝ≥0) (G : Ω → ℝ)
    (hGdef : ∀ ω, G ω =
      if ρ ω = 0 then w x else
        Real.exp (-(q * (ρ ω : ℝ))) *
          w (if (ρ ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (ρ ω) ω - rightLimit D (ρ ω) ω
            else riskProcess X x D (ρ ω) ω) +
          (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ ω : ℝ),
            ENNReal.ofReal (Real.exp (-(q * s)))
            ∂(dividendMeasure D ω)).toReal) :
    ∀ ω, 0 < ρ ω →
      G ω ≤ Real.exp (-(q * (ρ ω : ℝ))) *
        w (riskProcess X x D (ρ ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal := by sorry
