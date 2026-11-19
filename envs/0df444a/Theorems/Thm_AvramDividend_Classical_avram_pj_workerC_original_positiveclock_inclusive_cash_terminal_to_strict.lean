-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_positiveclock_inclusive_cash_terminal_to_strict
-- name    : AvramDividend.Classical.avram_pj_workerC_original_positiveclock_inclusive_cash_terminal_to_strict
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T00:46:08.006193+00:00
-- url     : https://prove2.me/theorems/23904f78-ca64-4fe9-8183-ae77eb3d17ac
-- title:
--   On original positive stopped-clock paths, inclusive postpayment payoff is bounded by prepayment strict cash plus true reserve terminal
-- statement:
--   For the exact original G reward with special value w(x) when rho=0, every path rho>0 satisfies G <= discounted w(true riskProcess at rho) plus cash strictly before rho, including correct terminal ruin contact. This imports Proved b244 while discharging the mismatch at zero clock by using a standard full F and showing G=F on the positive event.
-- source:
--   Public Proved 8066526a original true ruinclipped positive-stop inclusive Iic cash terminal contact <= strict, with exact original G hGdef.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_b244_original_ruinclipped_positive_stop_inclusive_Iic_cash_terminal_contact_le_strict
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_original_positiveclock_inclusive_cash_terminal_to_strict
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (hjump : ∀ η (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D η) →
      rightLimit D t η - D t η ≤
        w (riskProcess X x D t η) -
          w (riskProcess X x D t η -
            (rightLimit D t η - D t η)))
    (ρ : Ω → ℝ≥0) (G : Ω → ℝ)
    (hGdef : ∀ ω, G ω =
      (if ρ ω = 0 then w x else
        Real.exp (-(q * (ρ ω : ℝ))) *
          w (if (ρ ω : ℝ≥0∞) < ruinTime X x D ω then
              x + X.X (ρ ω) ω - rightLimit D (ρ ω) ω
            else riskProcess X x D (ρ ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal)) :
    ∀ ω, 0 < ρ ω →
      G ω ≤ Real.exp (-(q * (ρ ω : ℝ))) *
        w (riskProcess X x D (ρ ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal := by sorry
