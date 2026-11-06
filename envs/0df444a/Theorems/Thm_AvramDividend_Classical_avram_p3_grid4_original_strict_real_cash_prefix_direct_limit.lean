-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_strict_real_cash_prefix_direct_limit
-- name    : AvramDividend.Classical.avram_p3_grid4_original_strict_real_cash_prefix_direct_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:03:02.180203+00:00
-- url     : https://prove2.me/theorems/670d403d-b220-4479-ac58-f62fa4dd038f
-- title:
--   Original exact strict stopped real cash is the limit of increasing true payment prefixes
-- statement:
--   The original admissible dividend measure, stopped by the exact ruinTime and strict Iio real horizon, has real-valued discounted cash equal to the limit of its shrinking-width strict inner prefixes. The proof independently establishes the genuine measurable set union, uses continuity of the original weighted Stieltjes measure from below, and proves the full strict limit is finite from the accepted original closed Iic cash bound. Conversion to Real is justified by the pinned ENNReal.tendsto_toReal theorem. This original-source physical cash result contributes the cash part of the F_n Fatou liminf, retaining the time-zero right atom and excluding the T horizon right atom.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_original_strict_real_cash_prefix_direct_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D) (ω : Ω)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) (hT : 0 < T)
    (δ : ℕ → ℝ) (hδpos : ∀ n, 0 < δ n)
    (hδanti : Antitone δ) (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal)
      atTop
      (𝓝 ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal)) := by sorry
