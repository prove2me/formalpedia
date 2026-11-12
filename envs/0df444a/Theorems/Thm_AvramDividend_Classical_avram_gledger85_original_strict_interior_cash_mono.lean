-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger85_original_strict_interior_cash_mono
-- name    : AvramDividend.Classical.avram_gledger85_original_strict_interior_cash_mono
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T09:41:45.283227+00:00
-- url     : https://prove2.me/theorems/40d25e00-fc2e-44a9-b024-b4cf188e96e4
-- title:
--   Original strictly interior stopped cash cell lies in the full strict cash region
-- statement:
--   The original discounted dividend lintegral over an interior physical cell ending strictly before rho is bounded by the complete strict stopped discounted cash integral up to rho, with the same paymentTimes and dividendMeasure. This is the physical active-cell inclusion used alongside gledger83 in the gledger81 contact ledger.
-- source:
--   Original trajectory strictly interior cash-cell integral inclusion, a genuine active-cell aggregation prerequisite for gledger81 16e988d7.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger85_original_strict_interior_cash_mono
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (q : ℝ) (ρ a b : ℝ≥0) (hb : b < ρ) :
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Ioc (a : ℝ) (b : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
      ∂(dividendMeasure D ω)) ≤
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
      ∂(dividendMeasure D ω)) := by sorry
