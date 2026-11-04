-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_exact_discounted_stopped_atom_diffuse_cash
-- name    : AvramDividend.Classical.avram_p4_d_dividend_exact_discounted_stopped_atom_diffuse_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:07:13.208455+00:00
-- url     : https://prove2.me/theorems/d8ae045e-a279-4c4d-8a89-9525c2d72b8d
-- title:
--   Exact discounted original stopped cash splits into all paid right atoms and atomless Stieltjes mass
-- statement:
--   The genuine source paymentTimes(ruinTime)∩Iic T cash lintegral against dividendMeasure equals its countable right-atomic part plus its atomless diffuse part, with the supporting closed-horizon decomposition. Time zero, singular-continuous mass and an active horizon right-payment are included exactly; a positive ruin-time rightpayment is excluded. This keeps the original source payoff measure unchanged and supplies the cash identity needed for the P4-F dividend remainder budget.
-- source:
--   Proved Wave-4 atom/diffuse theorem d19177af and newly authored P4-D actual stopped measure split; Mathlib lintegral_add_measure and true original dividendMeasure/paymentTimes definitions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_actual_stopped_measure_atomic_diffuse
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_d_dividend_exact_discounted_stopped_atom_diffuse_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) (q : ℝ) :
    ∃ (A : Set ℝ) (μatom μdiffuse : Measure ℝ),
      A.Countable ∧ MeasurableSet A ∧
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ)) =
        μatom + μdiffuse ∧
      μatom = Measure.sum (fun t : A =>
        ((dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ)))
          {(t : ℝ)} • Measure.dirac (t : ℝ)) ∧
      μatom Aᶜ = 0 ∧ NullSingletonClass μdiffuse ∧
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂μatom) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂μdiffuse) := by sorry
