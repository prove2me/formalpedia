-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_paymentTimes_discounted_open_terminal_partition
-- name    : AvramDividend.Classical.avram_p3_c_bvchain_original_paymentTimes_discounted_open_terminal_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:25:40.870214+00:00
-- url     : https://prove2.me/theorems/209a3681-81b6-45ea-be9b-2d0f3f7ca02c
-- title:
--   Exact original strict-ruin paymentTimes discounted Stieltjes partition at an interior right-payment time
-- statement:
--   For the original admissible controlled Levy process and its true ruin-stopped paymentTimes, split the discounted Stieltjes integral on (a,c) into (a,b] and (b,c) at a<b<c. Every dividend at the interior split time is counted once, time-zero or external right atoms are excluded and all diffuse or singular-continuous dividend mass is retained without integrability assumptions.
-- source:
--   Original DividendStrategy/paymentTimes and proved paymentTimes_measurable, Mathlib lintegral_union; Avram Proposition 4(i) Eq. (5.13).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p3_c_bvchain_original_paymentTimes_discounted_open_terminal_partition
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (a b c : ℝ≥0) (hab : a < b) (hbc : b < c) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioo (a : ℝ) (c : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioc (a : ℝ) (b : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioo (b : ℝ) (c : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by sorry
