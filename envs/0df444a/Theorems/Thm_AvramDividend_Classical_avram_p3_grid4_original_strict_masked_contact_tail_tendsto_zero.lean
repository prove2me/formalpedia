-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_strict_masked_contact_tail_tendsto_zero
-- name    : AvramDividend.Classical.avram_p3_grid4_original_strict_masked_contact_tail_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T22:29:51.673541+00:00
-- url     : https://prove2.me/theorems/7c53ca0f-1669-4de9-9ef4-54e7198abaaf
-- title:
--   Original stopped discounted strictly left contact cash tends to zero without the right atom
-- statement:
--   For the actual original spectrally negative Levy X and admissible dividend strategy D, discounted stopped paymentTimes cash on shrinking strict-open Ioo tails below tau tends to zero, even if the dividend measure has an atom exactly at tau. The proof uses the established endpoint intersection, antitone sets and finite original stopped discounted cash, preserving the horizon and ruin payment conventions.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_masked_contact_tail_intersection_eq_endpoint
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_original_strict_masked_contact_tail_tendsto_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (T τ : ℝ≥0) (hτT : τ ≤ T)
    (δ : ℕ → ℝ) (hδpos : ∀ n, 0 < δ n)
    (hδanti : Antitone δ)
    (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Ioo ((τ : ℝ) - δ n) (τ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
      atTop (𝓝 0) := by sorry
