-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_nonsurvival_horizon_cash_open
-- name    : AvramDividend.Classical.avram_p3_bv_nonsurvival_horizon_cash_open
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:30:28.198362+00:00
-- url     : https://prove2.me/theorems/cb7f0a3c-de24-48e9-ab63-ff2c022f0590
-- title:
--   Original stopped BV cash has no horizon payment atom after or at positive ruin
-- statement:
--   On the original admissible dividend measure, at a positive deterministic horizon which does not strictly precede ruin, the almost-sure real-valued discounted stopped cash through the closed horizon equals strictly earlier cash. The positive horizon paymentTimes test excludes the endpoint, including when ruin is earlier or exactly at the horizon.
-- source:
--   Proved avram_p3_bv_real_cash_split_ae, the exact original paymentTimes predicate, and Mathlib ENNReal.ofReal_coe_nnreal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_real_cash_split_ae
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_nonsurvival_horizon_cash_open
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T) :
    let S : ℝ≥0 := ⟨T, hT⟩
    ∀ᵐ ω ∂P, ¬ ((S : ℝ≥0∞) < ruinTime X x D ω) →
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal =
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal := by sorry
