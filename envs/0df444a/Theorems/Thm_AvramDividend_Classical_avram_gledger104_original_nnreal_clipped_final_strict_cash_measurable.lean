-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger104_original_nnreal_clipped_final_strict_cash_measurable
-- name    : AvramDividend.Classical.avram_gledger104_original_nnreal_clipped_final_strict_cash_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T12:52:17.374012+00:00
-- url     : https://prove2.me/theorems/128f68b1-4b4c-4c43-953f-20ceff6bc0dc
-- title:
--   Original NNReal-subtracted random final strict dividend strip is measurable
-- statement:
--   The literal original same-space discounted Stieltjes dividend mass in the open final strip cut off by truncated NNReal subtraction is a measurable function of the sample. This is the exact interval in gledger39, avoiding an unjustified replacement by real subtraction that would include a different time-zero atom.
-- source:
--   Direct adaptation of accepted original moving interval kernel proof p3_grid3 for clipped NNReal endpoints in gledger39.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger104_original_nnreal_clipped_final_strict_cash_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (ρ : Ω → ℝ≥0) (hρ : Measurable ρ) (δ : ℝ≥0) :
    Measurable (fun ω : Ω =>
      ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Ioo ((ρ ω - δ : ℝ≥0) : ℝ) (ρ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)) := by sorry
