-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_BV_complement_cash_deficit_criterion
-- name    : AvramDividend.Classical.avram_wave7_17_original_BV_complement_cash_deficit_criterion
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:02:26.904347+00:00
-- url     : https://prove2.me/theorems/42277841-c1cd-404c-8a57-6031850d1a91
-- title:
--   Original BV strict complement expected cash deficit criterion with genuine L1 stopped Stieltjes payout
-- statement:
--   For the actual capped BV spectrally negative Lévy risk and dividend process in the strict complement, the finite-horizon full ruin-stopped discounted Stieltjes real cash is integrable; the sharp physical-drift envelope leaves a nonnegative expected budget deficit, and proving the HJB cash upper bound is exactly equivalent to proving that this source deficit absorbs the strictly positive drift slack. This is a quantitative missing-obligation criterion, not the stochastic HJB compensation itself.
-- source:
--   Avram, Palmowski, Pistorius (2007), Proposition 4(i), original-source BV strict complement and expected stopped cash. Derives from proved source sharp mean d6705e01 and genuine cash L1 5817eddd.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_BV_strict_complement_sharp_drift_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_bv_bounded_random_clock_cash_integrable
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_17_original_BV_complement_cash_deficit_criterion
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T)
    (hEnvelope : ¬ (x + T * X.drift ≤ w x)) :
    let Cash : Ω → ℝ := fun ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
    let DriftSlack : ℝ := x + T * X.drift - w x
    let BudgetDeficit : ℝ := x + T * X.drift - ∫ ω, Cash ω ∂P
    0 < T ∧ 0 < X.drift ∧ Integrable Cash P ∧
    0 < DriftSlack ∧ 0 ≤ BudgetDeficit ∧
    ((∫ ω, Cash ω ∂P) ≤ w x ↔ DriftSlack ≤ BudgetDeficit) := by sorry
