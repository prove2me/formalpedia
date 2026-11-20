-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_true_closed_prefix_plus_crossing_Ioc_cash_partition
-- name    : AvramDividend.Classical.avram_jump6_B_original_true_closed_prefix_plus_crossing_Ioc_cash_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T19:49:50.220885+00:00
-- url     : https://prove2.me/theorems/a90ebecf-2247-485b-ac87-2a53295e1719
-- title:
--   True original stopped discounted cash splits into closed prefix and crossing open-closed cell
-- statement:
--   The authentic original dividend paymentTimes mass up to a later clock b decomposes exactly into the mass up to and including the earlier clock a plus mass in Ioc(a,b). This is a disjoint restricted-lintegral identity retaining the initial payment atom, the actual ruin restriction, and every later payment, including the correct right-endpoint clock convention.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_paymentTimes_measurableSet
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_jump6_B_original_true_closed_prefix_plus_crossing_Ioc_cash_partition
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (a b : ℝ) (hab : a ≤ b) :
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic b,
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) =
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic a,
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) +
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Ioc a b,
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) := by sorry
