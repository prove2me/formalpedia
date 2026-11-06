-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_strict_cash_mesh_le_unfiltered
-- name    : AvramDividend.Classical.avram_p3_2_original_strict_cash_mesh_le_unfiltered
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T00:25:51.959649+00:00
-- url     : https://prove2.me/theorems/a1529e64-816e-4887-ba59-3c4cfb04ba05
-- title:
--   Original strict pre-T stopped-grid cash is bounded by the unfiltered physical cell cash
-- statement:
--   For the original dividendMeasure of X and D, the sum of nonnegative cash integrals restricted to actual paymentTimes, strictly before T, on each stopped physical interval is bounded by the same grid without the extra Iio T restriction.
-- source:
--   Pinned Mathlib MeasureTheory.lintegral_mono_set and Finset.sum_le_sum, with exact original dividendMeasure, ruin time and paymentTimes.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_strict_cash_mesh_le_unfiltered
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (T : ℝ≥0) (m n : ℕ) (f : ℝ → ℝ≥0∞) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun j =>
      min (((min j (m + 1) : ℕ) : ℝ≥0) *
        (T / (m + 1))) τ
    (∑ i ∈ Finset.range n,
      ∫⁻ t in (paymentTimes (ruinTime X x D ω) ∩
        Iio (T : ℝ)) ∩ Ioc (u i : ℝ) (u (i + 1) : ℝ),
        f t ∂(dividendMeasure D ω)) ≤
    (∑ i ∈ Finset.range n,
      ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Ioc (u i : ℝ) (u (i + 1) : ℝ),
        f t ∂(dividendMeasure D ω)):= by sorry
