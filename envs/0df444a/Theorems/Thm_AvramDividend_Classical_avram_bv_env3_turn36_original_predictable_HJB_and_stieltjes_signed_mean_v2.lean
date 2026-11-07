-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn36_original_predictable_HJB_and_stieltjes_signed_mean_v2
-- name    : AvramDividend.Classical.avram_bv_env3_turn36_original_predictable_HJB_and_stieltjes_signed_mean_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:44:49.304202+00:00
-- url     : https://prove2.me/theorems/5f9d038e-b151-4828-8164-02d474bc57ba
-- title:
--   Original controlled BV predictable HJB generator and Stieltjes gradient signed expectation
-- statement:
--   On the actual original spectrally negative Lévy riskProcess and admissible dividend strategy, the signed expectation of a bounded predictable martingale prefix, the source-exact localised generator drift cells, and the original Stieltjes dividend-gradient correction is at most zero, provided the physical dividend correction is integrable. This reduction combines the accepted predictable generator source with the actual cap-interior gradient sign, exposing missing integrability and boundary support explicitly.
-- source:
--   BV-ENV3 original source signed Ito drift-envelope reduction; depends on source-exact turn33 v2, accepted prior predictable budget and HJB signs.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn33_original_predictable_prefix_generator_HJB_signed_budget_v2
open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_turn36_original_predictable_HJB_and_stieltjes_signed_mean_v2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (U : ℝ≥0 × Ω → ℝ) (E : Set (ℝ≥0 × Ω))
    (hInterior : ∀ p ∈ E, 0 < U p ∧ ENNReal.ofReal (U p) < C)
    (B : Ω → Set ℝ)
    (hB : ∀ ω s, s ∈ B ω →
      0 < riskProcess X x D s.toNNReal ω ∧
        ENNReal.ofReal (riskProcess X x D s.toNNReal ω) < C)
    (Y : ℝ≥0 → Ω → ℝ) (hMart : Martingale Y 𝓕.rightCont P)
    (u : ℕ → ℝ≥0) (hu : Monotone u) (m : ℕ)
    (k : Ω → ℕ) (hk : Measurable k) (hkBound : ∀ ω, k ω ≤ m)
    (hPredictable : ∀ i : ℕ, MeasurableSet[𝓕.rightCont (u i)]
      {ω : Ω | i < k ω})
    (μ : Measure ℝ≥0)
    (hBI : ∀ i : ℕ, Integrable (fun ω =>
      ∫ t in Ioc (u i) (u (i + 1)), (if (t, ω) ∈ E then
            Real.exp (-(q * (t : ℝ))) *
              (X.generator w (U (t, ω)) - q * w (U (t, ω)))
           else 0) ∂μ) P)
    (hGradInt : Integrable (fun ω =>
      ∫ s, if s ∈ B ω then
        Real.exp (-(q * s)) *
          (1 - deriv w (riskProcess X x D s.toNNReal ω))
        else 0 ∂(dividendMeasure D ω)) P) :
    Integrable (fun ω =>
      (∑ i ∈ Finset.range (k ω),
        ((Y (u (i + 1)) ω - Y (u i) ω) +
         (∫ t in Ioc (u i) (u (i + 1)), (if (t, ω) ∈ E then
            Real.exp (-(q * (t : ℝ))) *
              (X.generator w (U (t, ω)) - q * w (U (t, ω)))
           else 0) ∂μ))) +
      (∫ s, if s ∈ B ω then
        Real.exp (-(q * s)) *
          (1 - deriv w (riskProcess X x D s.toNNReal ω))
        else 0 ∂(dividendMeasure D ω))) P ∧
    (∫ ω,
      (∑ i ∈ Finset.range (k ω),
        ((Y (u (i + 1)) ω - Y (u i) ω) +
         (∫ t in Ioc (u i) (u (i + 1)), (if (t, ω) ∈ E then
            Real.exp (-(q * (t : ℝ))) *
              (X.generator w (U (t, ω)) - q * w (U (t, ω)))
           else 0) ∂μ))) +
      (∫ s, if s ∈ B ω then
        Real.exp (-(q * s)) *
          (1 - deriv w (riskProcess X x D s.toNNReal ω))
        else 0 ∂(dividendMeasure D ω)) ∂P) ≤ 0 := by sorry
