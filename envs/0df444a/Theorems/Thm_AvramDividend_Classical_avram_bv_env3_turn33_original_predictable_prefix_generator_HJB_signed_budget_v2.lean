-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn33_original_predictable_prefix_generator_HJB_signed_budget_v2
-- name    : AvramDividend.Classical.avram_bv_env3_turn33_original_predictable_prefix_generator_HJB_signed_budget_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:29:59.609322+00:00
-- url     : https://prove2.me/theorems/6192c2d2-dd28-4839-8438-0db3441f2173
-- title:
--   Original stopped predictable prefix martingale with literal HJB generator signed budget (scoped summands)
-- statement:
--   For the original spectrally negative Levy X, a genuine right-continuous-filtration martingale Y and predictable bounded stopping selector k have an integrable finite physical-grid sum of original martingale increments and the actual discounted original generator HJB drift on strictly interior controlled-reserve events, with expected sum nonpositive. Explicitly retains the true generator, physical source reserve and cell integrability, and does not claim construction of Y, source Ito or Stieltjes limit.
-- source:
--   Source-exact composition of publicly Proved original predictable stopped signed budget 2b993cd3 and original HJB generator sign 72d2000c. Original BV pathwise Ito decomposition and actual stopped source construction are separate outstanding tasks. Corrected explicit nested sum-integral binder scope after publication diagnostic Unknown identifier i in initial proposal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn26_original_localised_HJB_signed_density_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn29_original_source_predictable_bounded_prefix_signed_budget
open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_turn33_original_predictable_prefix_generator_HJB_signed_budget_v2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (U : ℝ≥0 × Ω → ℝ) (E : Set (ℝ≥0 × Ω))
    (hInterior : ∀ p ∈ E, 0 < U p ∧ ENNReal.ofReal (U p) < C)
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
           else 0) ∂μ) P) :
    Integrable (fun ω =>
      ∑ i ∈ Finset.range (k ω),
        ((Y (u (i + 1)) ω - Y (u i) ω) +
        (∫ t in Ioc (u i) (u (i + 1)), (if (t, ω) ∈ E then
              Real.exp (-(q * (t : ℝ))) *
                (X.generator w (U (t, ω)) - q * w (U (t, ω)))
             else 0) ∂μ))) P ∧
    (∫ ω, ∑ i ∈ Finset.range (k ω),
      ((Y (u (i + 1)) ω - Y (u i) ω) +
      (∫ t in Ioc (u i) (u (i + 1)), (if (t, ω) ∈ E then
            Real.exp (-(q * (t : ℝ))) *
              (X.generator w (U (t, ω)) - q * w (U (t, ω)))
           else 0) ∂μ)) ∂P) ≤ 0 := by sorry
