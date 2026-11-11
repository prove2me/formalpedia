-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18_finite_range_optional_condexp_zero
-- name    : AvramDividend.Classical.avram_ja18_finite_range_optional_condexp_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T20:37:28.687877+00:00
-- url     : https://prove2.me/theorems/43ecbcfb-bf2f-4e80-b6d1-fc040639220f
-- title:
--   Original right-continuous L1 martingale AE identities support finite-range optional centring
-- statement:
--   Any integrable real field having all deterministic-time original right-continuous-filtration conditional expectation identities and AE zero initial value has integrable, conditionally centred value at a bounded stopping time taking only finitely many values. The field need only be AE adapted at each deterministic time; use the conditional expectation field as a strongly adapted modification and finite-range AE comparison.
-- source:
--   Genuine finite-grid optional-sampling component for 2d92580d and 61f39bfe. Mathlib Martingale.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range and right-continuous stopping sigma algebra; companion task transfers finite-grid results through right-continuous dominated limiting paths.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18_finite_range_optional_condexp_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (J : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0) (T : ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτT : ∀ ω, τ ω ≤ T)
    (F : Finset ℝ≥0) (hτF : ∀ ω, τ ω ∈ F)
    (hInt : ∀ t, Integrable (J t) P)
    (hMart : ∀ s t : ℝ≥0, s ≤ t →
      ∀ᵐ ω ∂P, condExp (𝓕.rightCont s) P (J t) ω = J s ω)
    (hZero : ∀ᵐ ω ∂P, J 0 ω = 0) :
    Integrable (fun ω => J (τ ω) ω) P ∧
    (∀ᵐ ω ∂P,
      condExp (𝓕.rightCont 0) P (fun ω => J (τ ω) ω) ω = 0) := by sorry
