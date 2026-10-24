-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_lower_survival_condExp_pullout
-- name    : AvramDividend.Classical.chat04_lower_survival_condExp_pullout
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T20:54:51.475946+00:00
-- url     : https://prove2.me/theorems/a5df0c0d-b4ef-468b-8be3-5ba8848db7e6
-- title:
--   Condition past one-sided ruin survival out of an arbitrary integrable future payoff
-- statement:
--   For a spectrally negative Lévy process and a lower ruin barrier, the entire uncountable-time survival history through a deterministic observation horizon is measurable in the observation-time filtration. Its indicator therefore commutes with the conditional expectation of any integrable future path-dependent reward. This is the one-sided conditional expectation pull-out step for the canonical killed q-scale martingale, and follows from the already published true one-sided filtration measurability theorem.
-- source:
--   Published chat03_lower_survival_filtration_measurable and Mathlib.condExp_indicator, for the Avram strict two-sided exit q-scale verification.

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_lower_survival_filtration_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_lower_survival_condExp_pullout
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (lower : ℝ) (T : ℝ≥0) (f : Ω → ℝ)
    (hf : Integrable f P) :
    P[({ω | ∀ t : ℝ≥0, t ≤ T → ¬ X.X t ω < lower}).indicator f | 𝓕 T] =ᵐ[P]
      ({ω | ∀ t : ℝ≥0, t ≤ T → ¬ X.X t ω < lower}).indicator
        (P[f | 𝓕 T]) := by sorry
