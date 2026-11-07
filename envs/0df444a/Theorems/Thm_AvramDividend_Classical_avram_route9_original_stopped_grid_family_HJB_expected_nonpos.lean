-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_route9_original_stopped_grid_family_HJB_expected_nonpos
-- name    : AvramDividend.Classical.avram_route9_original_stopped_grid_family_HJB_expected_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T12:32:23.7249+00:00
-- url     : https://prove2.me/theorems/1b32415a-6708-4231-8b4b-63c546c7c8c6
-- title:
--   Original stopped BV uniformly selected physical-grid HJB has nonpositive integrable expectation
-- statement:
--   For any family of original capped BV dividend physical grids and genuine right-continuous stopping clocks with strict interior reserve nodes, one may choose measurably and predictably the stopped prefix on every grid; the full discounted original generator plus dividend-gradient HJB sum has nonpositive integral whenever integrable. This leaves the exact cash/product source identity and positive approximation error as separate genuine obligations.
-- source:
--   Exact family-wise source reduction from the Proved original stopped predictable-prefix full HJB sign 95fdc3a3, intended for source c1e2f021 and cofinal b39f2dd1. The result is conditional only on actual stopped-interior and integrability side conditions; no artificial process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_route9_original_stopped_grid_family_HJB_expected_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (τ : ℕ → Ω → WithTop ℝ≥0)
    (hStop : ∀ n, IsStoppingTime 𝓕.rightCont (τ n))
    (u : ℕ → ℕ → ℝ≥0) (hu : ∀ n, Monotone (u n))
    (m : ℕ → ℕ)
    (hInterior : ∀ n ω i, i < m n →
      (u n i : WithTop ℝ≥0) < τ n ω →
      0 < riskProcess X x D (u n i) ω ∧
        ENNReal.ofReal (riskProcess X x D (u n i) ω) < C) :
    ∃ k : ℕ → Ω → ℕ,
      (∀ n ω, k n ω ≤ m n) ∧
      (∀ n ω i, i < m n →
        ((u n i : WithTop ℝ≥0) < τ n ω ↔ i < k n ω)) ∧
      (∀ n i, MeasurableSet[𝓕.rightCont (u n i)]
        {ω : Ω | i < k n ω}) ∧
      (∀ n (s : Set ℕ), MeasurableSet ((k n) ⁻¹' s)) ∧
      (∀ n,
        let G : Ω → ℝ := fun ω =>
          ∑ i ∈ Finset.range (k n ω),
            Real.exp (-(q * (u n i : ℝ))) *
              (((u n (i + 1) : ℝ) - (u n i : ℝ)) *
                (X.generator w (riskProcess X x D (u n i) ω) -
                  q * w (riskProcess X x D (u n i) ω)) +
              (D (u n (i + 1)) ω - D (u n i) ω) *
                (1 - deriv w (riskProcess X x D (u n i) ω)))
        Integrable G P → (∫ ω, G ω ∂P) ≤ 0) := by sorry
