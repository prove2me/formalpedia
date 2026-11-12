-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger107_original_ruinclipped_mesh_error_pointwise_bound
-- name    : AvramDividend.Classical.avram_gledger107_original_ruinclipped_mesh_error_pointwise_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T13:05:39.46735+00:00
-- url     : https://prove2.me/theorems/da5c050a-3ea7-4a75-ba2b-789c682a7806
-- title:
--   Each original ruin-clipped physical mesh error is pointwise dominated by the real-mesh cash envelope
-- statement:
--   For each original path, the nonnegative physical mesh error is bounded by the real-subtracted strict cash envelope. One part uses the discounted cash bound for unweighted pre-ruin dividend mass; the other is the monotonic clipped-to-real final interval. This is the pointwise comparison needed for gledger39.
-- source:
--   Assembles gledger105 plus gledger106 into the exact pointwise inequality for gledger39.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger107_original_ruinclipped_mesh_error_pointwise_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q) (n ρ δ : ℝ≥0)
    (hρn : ρ ≤ n) (hρruin : (ρ : ℝ≥0∞) ≤ ruinTime X x D ω) :
    q * (δ : ℝ) * (dividendMeasure D ω (Ioo (0 : ℝ) (ρ : ℝ))).toReal +
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Ioo ((ρ - δ : ℝ≥0) : ℝ) (ρ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ≤
    q * (δ : ℝ) * Real.exp (q * (n : ℝ)) *
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Ioo ((ρ : ℝ) - (δ : ℝ)) (ρ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal := by sorry
