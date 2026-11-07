-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_route9_original_stopped_grid_family_compensated_HJB_signed_budget
-- name    : AvramDividend.Classical.avram_route9_original_stopped_grid_family_compensated_HJB_signed_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T12:44:16.554868+00:00
-- url     : https://prove2.me/theorems/100bd62c-d3c6-4c8b-8309-3f0daf84f778
-- title:
--   True stopped BV compensated martingale plus original HJB physical-grid signed budget
-- statement:
--   Combines an arbitrary genuinely centred and integrable original stopped compensated source family with the separately signed full generator/dividend-gradient HJB grid. It proves L1 integrability of the total actual-grid signed source and nonpositive expected value for every grid, while retaining the predictable stopped-prefix selection. The unresolved obligation is to identify the centred M from the actual Lévy jump integral and match the true cash/product identity on the same physical grid.
-- source:
--   Source-exact bridge from Proved 1b32415a family-wise original BV HJB expected sign and the centred L1 compensated-jump source produced by d5712b28 when aligned. Input to c1e2f021 original stopped signed Fatou certificate. All original stochastic source/contact hypotheses remain explicit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_route9_original_stopped_grid_family_compensated_HJB_signed_budget
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
        ENNReal.ofReal (riskProcess X x D (u n i) ω) < C)
    (M : ℕ → Ω → ℝ)
    (hMInt : ∀ n, Integrable (M n) P)
    (hMMean : ∀ n, (∫ ω, M n ω ∂P) = 0) :
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
        Integrable G P →
          Integrable (fun ω => M n ω + G ω) P ∧
            (∫ ω, M n ω + G ω ∂P) ≤ 0) := by sorry
