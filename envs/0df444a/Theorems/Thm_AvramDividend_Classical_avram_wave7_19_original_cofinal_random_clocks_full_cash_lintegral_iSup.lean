-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_cofinal_random_clocks_full_cash_lintegral_iSup
-- name    : AvramDividend.Classical.avram_wave7_19_original_cofinal_random_clocks_full_cash_lintegral_iSup
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:19:59.892129+00:00
-- url     : https://prove2.me/theorems/f06348b9-331b-447c-b4d3-98e69dd360a5
-- title:
--   Original weighted Stieltjes ruin cash is increasing supremum of any cofinal interior stopped-clock cash
-- statement:
--   For the exact original source dividendMeasure D along any fixed Levy path, any increasing sequence of extended stopping-clock values whose supremum is the actual ruinTime exhausts the full paymentTimes integral through an arbitrary real horizon T. The weighted Stieltjes integrals increase to the full nonnegative cash, retaining the initial right atom and excluding a strictly positive ruin right-payment. This takes the stopping-time construction supplied by W7-18 and proves the deterministic boundary monotone passage without continuity, finite total mass or uniform integrability.
-- source:
--   Source-specific paymentTimes cofinal clock union W7-19 bc92f7fc-528c-4211-9a52-f2735efe1bf5, Mathlib Set.indicator_iUnion_apply and lintegral_iSup.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_19_original_cofinal_random_clocks_full_cash_lintegral_iSup
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (σ : ℕ → ℝ≥0∞) (hσ : Monotone σ)
    (hSup : (⨆ k : ℕ, σ k) = ruinTime X x D ω) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
      ⨆ k : ℕ, (∫⁻ t in paymentTimes (σ k) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by sorry
