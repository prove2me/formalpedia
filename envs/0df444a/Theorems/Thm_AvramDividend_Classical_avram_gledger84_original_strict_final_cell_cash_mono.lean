-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger84_original_strict_final_cell_cash_mono
-- name    : AvramDividend.Classical.avram_gledger84_original_strict_final_cell_cash_mono
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T09:24:15.029754+00:00
-- url     : https://prove2.me/theorems/cc034a9a-c537-411c-a754-edbb42d7d8bf
-- title:
--   Original strict crossing-cell discounted cash lies in the final open mesh strip
-- statement:
--   For every original path, whenever the last physical cell starts no earlier than rho minus its mesh width, its strict discounted dividend cash (with paymentTimes intersected against the original ruin time) is bounded by the entire open terminal strip. This is a set-inclusion and restricted-lintegral monotonicity fact, with no assumption on reserve or global reward smoothness. It is the final-cell half of gledger81, where the stopped terminal right-payment atom must remain excluded.
-- source:
--   Genuine strict final-cell set/measure lemma needed in gledger81 16e988d7. Separate from the positive-prefix right endpoint estimate gledger83; avoids assuming nonnegative postpayment reserve on the ruin-crossing cell.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger84_original_strict_final_cell_cash_mono
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (q : ℝ) (ρ δ a : ℝ≥0)
    (ha : (ρ : ℝ) - (δ : ℝ) ≤ (a : ℝ))
    (hab : a ≤ ρ) :
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Ioo (a : ℝ) (ρ : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
      ∂(dividendMeasure D ω)) ≤
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
        Ioo ((ρ : ℝ) - (δ : ℝ)) (ρ : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
      ∂(dividendMeasure D ω)) := by sorry
