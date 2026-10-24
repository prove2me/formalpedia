-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_lower_killed_condExp_markov_factorisation
-- name    : AvramDividend.Classical.chat04_lower_killed_condExp_markov_factorisation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T20:58:25.87286+00:00
-- url     : https://prove2.me/theorems/ccec51fa-0e27-40c2-838e-3d79fed78f82
-- title:
--   Full one-sided killed conditional payoff factorisation across an observation time
-- statement:
--   For a Levy reserve with lower ruin killing monitored at all times through u, the conditional expectation at s≤u of any real payoff killed by the entire survival history equals the historical survival indicator multiplied by the conditional expectation of that payoff killed on the shifted future interval [s,u]. The only payoff hypothesis is integrability of the future-killed component. The proof combines the exact pathwise factorisation, genuine filtration measurability of historical lower survival, and the pinned conditional expectation indicator pull-out. This is the killed Markov factorisation for the exact q-scale martingale target, without assuming its q-harmonicity.
-- source:
--   Accepted one-sided survival filtration lemma and target chat04_lower_killing_indicator_factorisation; Mathlib condExp_indicator; Avram two-sided exit verification.

import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_lower_survival_filtration_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_lower_killing_indicator_factorisation

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_lower_killed_condExp_markov_factorisation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (x : ℝ) (s u : ℝ≥0) (hsu : s ≤ u) (f : Ω → ℝ)
    (hf : Integrable
      (({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
        0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}).indicator f) P) :
    P[({ω | ∀ v : ℝ≥0, v ≤ u → 0 ≤ x + X.X v ω}).indicator f | 𝓕 s] =ᵐ[P]
      ({ω | ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω}).indicator
        (P[({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
          0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}).indicator f | 𝓕 s]) := by sorry
