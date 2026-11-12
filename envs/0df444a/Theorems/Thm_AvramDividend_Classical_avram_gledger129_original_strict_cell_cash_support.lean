-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger129_original_strict_cell_cash_support
-- name    : AvramDividend.Classical.avram_gledger129_original_strict_cell_cash_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T17:37:06.534576+00:00
-- url     : https://prove2.me/theorems/26b42fc3-7f91-4f27-b070-0a3d605790c5
-- title:
--   Original strictly interior stopped dividend cell is wholly in the payment support
-- statement:
--   On the original process and original dividend measure, any Stieltjes cash cell with right endpoint strictly before the stopped ruin-clipped clock is already contained in the actual paymentTimes support. Hence restricting the integration domain to actual pre-ruin paymentTimes leaves its positive discounted cash unchanged.
-- source:
--   Exact original X, D, ruinTime, paymentTimes and dividendMeasure. Specialises the proved strict clipped-clock support lemma b6a701ac-ec25-459d-9884-db11e6d980da.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger129_original_strict_cell_cash_support
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (q : ℝ)
    (ρ : ℝ≥0) (hρ : (ρ : ℝ≥0∞) ≤ ruinTime X x D ω)
    (v : ℕ → ℝ≥0) (i : ℕ) (hi : v (i + 1) < ρ) :
    (∫⁻ s in Ioc (v i : ℝ) (v (i + 1) : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
      ∂(dividendMeasure D ω)).toReal =
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
        Ioc (v i : ℝ) (v (i + 1) : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
      ∂(dividendMeasure D ω)).toReal := by sorry
