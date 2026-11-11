-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18_original_dominated_martingale_limit
-- name    : AvramDividend.Classical.avram_ja18_original_dominated_martingale_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T22:12:37.285912+00:00
-- url     : https://prove2.me/theorems/e849c81a-5307-4233-b00a-81580a2e5389
-- title:
--   Dominated cutoff martingales pass to same-filtration deterministic-time martingale limit
-- statement:
--   Given martingales J_k on one original right-continuous filtration, simultaneous almost-sure cutoff convergence to adapted Z, and an integrable finite-horizon envelope for both limits and all cutoffs, prove Z integrable at all deterministic times and its conditional martingale identity. Use dominated convergence/conditional-expectation uniqueness; mathematically independent of the physical marked point process.
-- source:
--   Pure measure-theoretic and original-filtration transfer child of 096ba1c2; reuse Proved 470a6b58 and pinned Mathlib tendsto_condExp_unique, requiring actual original cutoff identities from Proved c321c303.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18_original_dominated_martingale_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (J : ℕ → ℝ≥0 → Ω → ℝ) (Z : ℝ≥0 → Ω → ℝ)
    (hInt : ∀ k t, Integrable (J k t) P)
    (hMart : ∀ (k : ℕ) (s t : ℝ≥0), s ≤ t →
      ∀ᵐ ω ∂P, condExp (𝓕.rightCont s) P (J k t) ω = J k s ω)
    (hLimit : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k => J k t ω) atTop (𝓝 (Z t ω)))
    (hSelf : ∀ t : ℝ≥0, ∀ᵐ ω ∂P,
      condExp (𝓕.rightCont t) P (Z t) ω = Z t ω)
    (hBounds : ∀ T : ℝ≥0, ∃ B : Ω → ℝ,
      Integrable B P ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ T → ‖Z t ω‖ ≤ B ω) ∧
      (∀ k : ℕ, ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ T →
        ‖J k t ω‖ ≤ B ω)) :
    (∀ t : ℝ≥0, Integrable (Z t) P) ∧
    (∀ s t : ℝ≥0, s ≤ t →
      ∀ᵐ ω ∂P, condExp (𝓕.rightCont s) P (Z t) ω = Z s ω) := by sorry
