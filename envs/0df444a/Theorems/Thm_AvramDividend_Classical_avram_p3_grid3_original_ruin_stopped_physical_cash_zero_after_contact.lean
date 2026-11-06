-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_physical_cash_zero_after_contact
-- name    : AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_physical_cash_zero_after_contact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:28:25.748321+00:00
-- url     : https://prove2.me/theorems/8cc2d3b2-6f1a-40e6-b07d-463122c73a11
-- title:
--   Original stopped ruin/horizon physical cells have zero literal discounted Stieltjes cash after contact
-- statement:
--   For the actual X, dividend strategy D, discount q and ruin-stopped physical grid, if the left endpoint has contacted tau, the entire subsequent exact paymentTimes (ruinTime X x D omega) intersection Ioc interval is empty. Thus its literal discounted dividendMeasure ENNReal lintegral is exactly zero; no terminal, ruin, cap or finiteness hypothesis.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_physical_flat_after_contact
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_physical_cash_zero_after_contact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (m : ℕ) (ω : Ω) (q : ℝ) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun k =>
      min (((min k (m + 1) : ℕ) : ℝ≥0) *
        (T / (m + 1))) τ
    ∀ i : ℕ, u i = τ →
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Ioc (u i : ℝ) (u (i + 1) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal = 0 := by sorry
