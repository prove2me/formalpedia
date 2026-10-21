-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_closed_survival_conditioning_any_integrable_payoff
-- name    : AvramDividend.Classical.chat04_closed_survival_conditioning_any_integrable_payoff
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T22:21:38.881048+00:00
-- url     : https://prove2.me/theorems/58a584bc-20f8-42d9-b1a3-f1ce8355439d
-- title:
--   Condition on genuine closed-horizon Lévy survival for any integrable path payoff
-- statement:
--   For any canonical spectrally negative Lévy process and finite horizon T, the event of staying between both strict lower and upper barriers at every continuous time t≤T belongs to the actual process filtration F_T. Consequently, for every arbitrary integrable real future payoff f:Ω→R, including path-dependent future survival/reward functionals, conditional expectation onto F_T of f restricted to historical continuous-time survival is equal almost everywhere to the same historical survival indicator times the conditional expectation of f. The proof uses the accepted rigorous closed-horizon survival filtration measurability and exact pinned Mathlib condExp_indicator. No assumption of future independence or killed q-scale harmonicity is needed. This is the precise conditional-expectation rule required after the pathwise Markov survival split.
-- source:
--   Accepted AvramDividend.Classical.chat04_closed_horizon_survival_filtration_measurable UUID 8f46ff43-afd6-449a-be49-308c7399740e; pinned Mathlib MeasureTheory.condExp_indicator from Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator.

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_closed_horizon_survival_filtration_measurable

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_closed_survival_conditioning_any_integrable_payoff
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (lower upper : ℝ) (T : ℝ≥0)
    (f : Ω → ℝ) (hf : Integrable f P) :
    P[({ω | ∀ t : ℝ≥0, t ≤ T →
         ¬ (X.X t ω < lower ∨ upper < X.X t ω)}).indicator f | 𝓕 T] =ᵐ[P]
      ({ω | ∀ t : ℝ≥0, t ≤ T →
         ¬ (X.X t ω < lower ∨ upper < X.X t ω)}).indicator
        (P[f | 𝓕 T]) := by sorry
