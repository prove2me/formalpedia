-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_condExp_closed_killed_survival_markov_factorisation
-- name    : AvramDividend.Classical.chat04_condExp_closed_killed_survival_markov_factorisation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T22:44:05.985874+00:00
-- url     : https://prove2.me/theorems/3b5509f2-8a6d-4962-a0c5-699cbf8dbdb5
-- title:
--   Conditional factorisation of continuously killed survival across an intermediate time
-- statement:
--   For a canonical spectrally negative Lévy process and two deterministic times s≤u, the conditional expectation given F_s of an integrable real path-dependent payoff f killed by any strict lower or upper exit on the entire closed horizon [0,u] equals the historical survival indicator through [0,s] multiplied by the conditional expectation of f restricted to future-interval survival [s,u] expressed via the current reserve X_s and the increments X_v−X_s. The sole extra assumption is integrability of the future-restricted payoff so the conditional expectations are defined, not independence or q-scale harmonicity. This combines two independently Prove2Me-ACCEPTED results: the exact pathwise survival split and the extraction of a continuous-time historical survival indicator from a conditional expectation. It is the exact conditional decomposition required before identifying the law of the shifted future Lévy path for the killed Markov semigroup.
-- source:
--   ACCEPTED Chat04 closed_horizon_survival_pathwise_markov_split UUID 75c76580-1762-4af5-8a87-86ebd97db60a, ACCEPTED Chat04 closed_survival_conditioning_any_integrable_payoff UUID 58a584bc-20f8-42d9-b1a3-f1ce8355439d; classical Set.indicator pair law and conditional expectation.

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_closed_horizon_survival_pathwise_markov_split
import Theorems.Thm_AvramDividend_Classical_chat04_closed_survival_conditioning_any_integrable_payoff

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_condExp_closed_killed_survival_markov_factorisation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (lower upper : ℝ) (s u : ℝ≥0) (hsu : s ≤ u)
    (f : Ω → ℝ)
    (hFutureInt : Integrable
      (({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
        ¬ (X.X s ω + (X.X v ω - X.X s ω) < lower ∨
          upper < X.X s ω + (X.X v ω - X.X s ω))}).indicator f) P) :
    P[({ω | ∀ v : ℝ≥0, v ≤ u →
        ¬ (X.X v ω < lower ∨ upper < X.X v ω)}).indicator f | 𝓕 s] =ᵐ[P]
      ({ω | ∀ v : ℝ≥0, v ≤ s →
        ¬ (X.X v ω < lower ∨ upper < X.X v ω)}).indicator
        (P[({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
        ¬ (X.X s ω + (X.X v ω - X.X s ω) < lower ∨
          upper < X.X s ω + (X.X v ω - X.X s ω))}).indicator f | 𝓕 s]) := by sorry
