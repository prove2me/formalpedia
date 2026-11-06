-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_original_strict_cash_postterminal_ofreal_exact
-- name    : AvramDividend.Classical.avram_limit2_original_strict_cash_postterminal_ofreal_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:55:10.827986+00:00
-- url     : https://prove2.me/theorems/b63961ce-10fa-496e-b505-501fcecf3570
-- title:
--   Exact original strict stopped cash plus nonnegative postterminal real-to-ENNReal identity
-- statement:
--   For the exact original stopped dividendMeasure cash through a strict real horizon Iio T, if the ENNReal cash integral is finite and the original real postpayment terminal is nonnegative, its real-sum positive-part embedding equals the ENNReal cash plus the embedded terminal, exactly. This is the missing local connector from the original signed BV Fatou grid certificate's ofReal (strictCash.toReal + terminal) into a nonnegative stopped cash-plus-terminal Fatou budget. Finiteness and terminal nonnegativity are explicit; no horizon atom or terminal is dropped.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_original_strict_cash_postterminal_ofreal_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (Term : ℝ) (hTerm : 0 ≤ Term)
    (hCashFinite : (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)) ≠ ⊤) :
    ENNReal.ofReal ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal + Term) =
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)) + ENNReal.ofReal Term := by sorry
