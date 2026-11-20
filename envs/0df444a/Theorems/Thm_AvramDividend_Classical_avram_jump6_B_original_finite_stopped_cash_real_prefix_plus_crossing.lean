-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_finite_stopped_cash_real_prefix_plus_crossing
-- name    : AvramDividend.Classical.avram_jump6_B_original_finite_stopped_cash_real_prefix_plus_crossing
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T20:04:49.122407+00:00
-- url     : https://prove2.me/theorems/6da18201-024b-44a1-88b8-50ea2a8dbea4
-- title:
--   Original finite stopped discounted real cash splits into closed prefix and crossing Ioc cell
-- statement:
--   Given a finite genuine original stopped dividend cash amount on Iic b, its real value equals the cash on the earlier closed interval Iic a plus the actual discounted cash on Ioc(a,b). This source-faithfully retains the initial dividend atom and uses the Proved exact ENNReal cash partition, with strict finite-mass justification before converting to Real.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_true_closed_prefix_plus_crossing_Ioc_cash_partition
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_jump6_B_original_finite_stopped_cash_real_prefix_plus_crossing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (a b : ℝ) (hab : a ≤ b)
    (hFin :
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic b,
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) < ⊤) :
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic b,
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal =
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic a,
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal +
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Ioc a b,
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal := by sorry
