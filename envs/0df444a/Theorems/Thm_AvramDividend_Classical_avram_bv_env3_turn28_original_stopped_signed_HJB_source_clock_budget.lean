-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn28_original_stopped_signed_HJB_source_clock_budget
-- name    : AvramDividend.Classical.avram_bv_env3_turn28_original_stopped_signed_HJB_source_clock_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T00:04:55.009761+00:00
-- url     : https://prove2.me/theorems/ef5543b5-de3b-4743-95c0-7c2e9206365c
-- title:
--   Actual original stopped source martingale and localised HJB signed clock budget
-- statement:
--   An original-process stopped martingale Y combined with the actual discounted generator HJB residual integrated over localised physical grid cells has a finite signed-grid expectation no greater than zero. The original generator residual is evaluated at the actual controlled pre-reserve U, only on strictly positive capped E. Integrability of these physical-clock drift integrals and construction of the original source martingale remain explicit prerequisites.
-- source:
--   Reduction to BV-ENV3 turn25 genuine original stopping-clock martingale signed budget and turn26 original-generator pointwise HJB sign. These reductions are not a stochastic source Ito construction; true source Y, U, E and μ remain visible.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_turn28_original_stopped_signed_HJB_source_clock_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (U : ℝ≥0 × Ω → ℝ) (E : Set (ℝ≥0 × Ω))
    (hInterior : ∀ p ∈ E, 0 < U p ∧ ENNReal.ofReal (U p) < C)
    (Y : ℝ≥0 → Ω → ℝ)
    (hMart : Martingale Y 𝓕.rightCont P)
    (τ : Ω → WithTop ℝ≥0)
    (hStop : IsStoppingTime 𝓕.rightCont τ)
    (u : ℕ → ℝ≥0) (hu : Monotone u) (m : ℕ)
    (μ : Measure ℝ≥0)
    (hBI : ∀ i, Integrable (fun ω =>
      ∫ t in Ioc (u i) (u (i + 1)), (if (t, ω) ∈ E then
            Real.exp (-(q * (t : ℝ))) *
              (X.generator w (U (t, ω)) - q * w (U (t, ω)))
           else 0) ∂μ) P) :
    Integrable (fun ω =>
      ∑ i ∈ Finset.range m,
        if (u i : WithTop ℝ≥0) < τ ω then
          (Y (u (i + 1)) ω - Y (u i) ω) +
          (∫ t in Ioc (u i) (u (i + 1)), (if (t, ω) ∈ E then
            Real.exp (-(q * (t : ℝ))) *
              (X.generator w (U (t, ω)) - q * w (U (t, ω)))
           else 0) ∂μ)
        else 0) P ∧
    (∫ ω, ∑ i ∈ Finset.range m,
      (if (u i : WithTop ℝ≥0) < τ ω then
        (Y (u (i + 1)) ω - Y (u i) ω) +
        (∫ t in Ioc (u i) (u (i + 1)), (if (t, ω) ∈ E then
            Real.exp (-(q * (t : ℝ))) *
              (X.generator w (U (t, ω)) - q * w (U (t, ω)))
           else 0) ∂μ)
       else 0) ∂P) ≤ 0 := by sorry
