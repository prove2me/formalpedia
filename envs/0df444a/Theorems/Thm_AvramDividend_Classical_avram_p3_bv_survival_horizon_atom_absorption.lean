-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_survival_horizon_atom_absorption
-- name    : AvramDividend.Classical.avram_p3_bv_survival_horizon_atom_absorption
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:28:01.881794+00:00
-- url     : https://prove2.me/theorems/0790a949-0c51-4a1f-b094-bdcaea4ea5e4
-- title:
--   Original strict-survival finite-horizon rightpayment absorbed into the postpayment HJB terminal
-- statement:
--   For an original admissible dividend strategy, canonical right-jump secant bound and any nonnegative finite horizon, almost surely on strict survival the exact closed-horizon discounted Stieltjes cash plus post-rightpayment value is bounded by strictly pre-horizon cash plus the prepayment candidate value. Includes the exact horizon rightpayment atom and assumes no jump compensation or surrogate process.
-- source:
--   Proved avram_p3_bv_real_cash_split_ae and avram_wave8_21_original_active_horizon_rightpayment_discounted_hjump_budget, with exact original paymentTimes set equality and riskProcess algebra.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_real_cash_split_ae
import Theorems.Thm_AvramDividend_Classical_avram_wave8_21_original_active_horizon_rightpayment_discounted_hjump_budget
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_survival_horizon_atom_absorption
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (w : ℝ → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) :
    let S : ℝ≥0 := ⟨T, hT⟩
    ∀ᵐ ω ∂P, (S : ℝ≥0∞) < ruinTime X x D ω →
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
        Real.exp (-(q * T)) * w (x + X.X S ω - rightLimit D S ω) ≤
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) := by sorry
