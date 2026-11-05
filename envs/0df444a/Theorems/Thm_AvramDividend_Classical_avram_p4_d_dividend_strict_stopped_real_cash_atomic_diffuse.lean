-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_strict_stopped_real_cash_atomic_diffuse
-- name    : AvramDividend.Classical.avram_p4_d_dividend_strict_stopped_real_cash_atomic_diffuse
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:19:52.458035+00:00
-- url     : https://prove2.me/theorems/8cd41687-b0b0-485e-b09f-80ffec5cfbae
-- title:
--   Actual strictly surviving original stopped Stieltjes cash splits into finite real-valued atomic and diffuse amounts
-- statement:
--   At an original pathwise finite horizon strictly before ruin with nonnegative discount, the full genuine paid Stieltjes ENNReal lintegral is finite by the Wave8 closed-horizon rightLimit bound. Combining this with the accepted source-exact atom/diffuse measure decomposition forces both discounted pieces finite and allows an honest ENNReal.toReal_add conversion: original real cash equals atomic real cash plus diffuse real cash. Both the initial right-payment and eligible horizon right-payment remain inside the atomic measure, while diffuse includes absolutely and singular continuous mass.
-- source:
--   Accepted P4-D exact original paid atomic/diffuse lintegral split UUID d8ae045e-a279-4c4d-8a89-9525c2d72b8d, proved Wave8 strict-survival discounted full cash bound UUID 86168e67-e783-4efd-8a01-225fc7a4a993, pinned ENNReal.add_lt_top and ENNReal.toReal_add.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_exact_discounted_stopped_atom_diffuse_cash
import Theorems.Thm_AvramDividend_Classical_avram_wave8_21_original_strict_survival_discounted_full_cash_le_rightLimit
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_strict_stopped_real_cash_atomic_diffuse
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (ω : Ω) (T : ℝ≥0)
    (hstrict : (T : ℝ≥0∞) < ruinTime X x D ω) :
    ∃ (A : Set ℝ) (μatom μdiffuse : Measure ℝ),
      A.Countable ∧ MeasurableSet A ∧
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ)) =
        μatom + μdiffuse ∧
      μatom = Measure.sum (fun t : A =>
        ((dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ)))
          {(t : ℝ)} • Measure.dirac (t : ℝ)) ∧
      μatom Aᶜ = 0 ∧ NullSingletonClass μdiffuse ∧
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂μatom) < ⊤ ∧
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂μdiffuse) < ⊤ ∧
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂μatom).toReal +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂μdiffuse).toReal := by sorry
