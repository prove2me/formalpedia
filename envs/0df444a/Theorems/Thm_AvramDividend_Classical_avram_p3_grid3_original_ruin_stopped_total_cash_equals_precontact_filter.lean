-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_total_cash_equals_precontact_filter
-- name    : AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_total_cash_equals_precontact_filter
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:46:23.378412+00:00
-- url     : https://prove2.me/theorems/71858d96-cef9-4b56-a90c-11289f31a5d2
-- title:
--   Original ruin-stopped physical grid total literal discounted cash is supported precisely on precontact cells
-- statement:
--   For the original spectral-negative Levy X and actual dividend strategy D, the finite stopped physical-grid discounted dividendMeasure cash sum equals its Finset.filter restriction to mesh cells whose left endpoint is strictly below tau=min(ruin,T). The proof uses the prior Proved exact cash-zero after contact theorem and monotonicity of min clamping, making all flat post-ruin/horizon cells disappear without modifying original cash, cap, or terminal conventions.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_physical_cash_zero_after_contact
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_total_cash_equals_precontact_filter
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (m n : ℕ) (ω : Ω) (q : ℝ) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun k =>
      min (((min k (m + 1) : ℕ) : ℝ≥0) *
        (T / (m + 1))) τ
    let cash : ℕ → ℝ := fun i =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Ioc (u i : ℝ) (u (i + 1) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal
    (∑ i ∈ Finset.range n, cash i) =
      ∑ i ∈ (Finset.range n).filter (fun i => u i < τ), cash i := by sorry
