-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_reward_L1_nonnegative
-- name    : AvramDividend.Classical.avram_p3_bv_original_strict_reward_L1_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:36:14.339076+00:00
-- url     : https://prove2.me/theorems/221852bf-aa9f-4363-a5ec-748346fdd1bc
-- title:
--   Actual original BV strictly stopped cash-plus-prepayment terminal is L1 and pointwise nonnegative
-- statement:
--   For the genuine original bounded-variation spectrally negative Lévy process and admissible dividends, the exact strict Iio T discounted Stieltjes cash includes the time-zero payment and is nonnegative. At T>0 the pre-rightpayment survival terminal is nonnegative by the original survivor hypothesis and positive discount. The already-Proved original strict joint L1 theorem establishes integrability. This is a concrete original-process candidate for the nonnegative Fatou payoff grid, without postulating an independent payoff integrability assumption.
-- source:
--   Proved original BV strict payoff L1 78fa7075 and exact source dividendMeasure, ruinTime definitions

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_prebudget_L1

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/- At positive time the actual original strict Stieltjes cash and
pre-rightpayment survival value form a nonnegative integrable reward.
This retains the zero-time dividend atom and original ruin predicate. -/

theorem AvramDividend.Classical.avram_p3_bv_original_strict_reward_L1_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω)) :
    let S : ℝ≥0 := ⟨T, hT⟩
    let Strict : Ω → ℝ := fun ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0)
    Integrable Strict P ∧ ∀ ω, 0 ≤ Strict ω := by sorry
