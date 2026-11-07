-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_route6_original_stopped_predictable_prefix_full_hjb_sign
-- name    : AvramDividend.Classical.avram_route6_original_stopped_predictable_prefix_full_hjb_sign
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T09:36:01.812522+00:00
-- url     : https://prove2.me/theorems/95fdc3a3-ba95-48ce-aceb-1a7cd7a91e8c
-- title:
--   Original stopped physical grid predictable measurable prefix has full BV HJB sign
-- statement:
--   Integrates the genuinely proved bounded predictable/measurable stopped-grid prefix selector with the genuinely proved physical generator-and-dividend HJB sign. It yields the exact stopped prefix mask, measurable index, predictable events, and discounted generator plus dividend gradient contribution nonpositive at all active original reserve nodes. The only remaining source side-condition is interior localisation; martingale compensation and endpoint atom accounting are independent.
-- source:
--   Bridge from public Proved bcd472a7 and c4fc3aa2 into the original BV stopped source finite-grid HJB sign. Intended input to c1e2f021 and b39f2dd1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_route6_original_stopped_predictable_prefix_full_hjb_sign
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
    (τ : Ω → WithTop ℝ≥0)
    (hStop : IsStoppingTime 𝓕.rightCont τ)
    (u : ℕ → ℝ≥0) (hu : Monotone u) (m : ℕ)
    (hInterior : ∀ ω i, i < m →
      (u i : WithTop ℝ≥0) < τ ω →
      0 < riskProcess X x D (u i) ω ∧
        ENNReal.ofReal (riskProcess X x D (u i) ω) < C) :
    ∃ k : Ω → ℕ,
      (∀ ω, k ω ≤ m) ∧
      (∀ ω i, i < m →
        ((u i : WithTop ℝ≥0) < τ ω ↔ i < k ω)) ∧
      (∀ i, MeasurableSet[𝓕.rightCont (u i)]
        {ω : Ω | i < k ω}) ∧
      (∀ s : Set ℕ, MeasurableSet (k ⁻¹' s)) ∧
      (∀ ω,
        (∑ i ∈ Finset.range (k ω),
          Real.exp (-(q * (u i : ℝ))) *
            (((u (i + 1) : ℝ) - (u i : ℝ)) *
              (X.generator w (riskProcess X x D (u i) ω) -
                q * w (riskProcess X x D (u i) ω)) +
            (D (u (i + 1)) ω - D (u i) ω) *
              (1 - deriv w (riskProcess X x D (u i) ω)))) ≤ 0) := by sorry
