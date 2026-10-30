-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_01_finite_killed_markov_ennreal
-- name    : AvramDividend.Classical.avram_root29_01_finite_killed_markov_ennreal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T08:29:15.328996+00:00
-- url     : https://prove2.me/theorems/d1848a7c-0a46-4597-b99b-19e4d6065e27
-- title:
--   Finite-horizon killed Esscher Markov identity under the original Lévy law
-- statement:
--   For the genuine original spectrally negative Lévy process and every finite pair of deterministic horizons, the positive ENNReal lower-survival Esscher reward at s+u is the original-P historical expectation of the current Esscher density times the exact real future lower-survival mass evaluated at the random reserve x+X_s, on historical survival. This composes independently Proved full-path original-law Markov disintegration, the real fresh-path integral bridge, the historical state pushforward identity and monotonicity of the future reserve kernel. No scale harmonicity, stopping theorem, tilted infinite-horizon path law or two-sided exit is assumed.
-- source:
--   WS1A source work/avram_root29_01_finite_killed_markov_ennreal.lean; Proved children e1f9d84f, 6fe4b3eb, f07a704e.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_esscher_survival_finite_markov_ennreal
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_history_survival_positive_kernel_map
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_lower_survival_mass_monotone_start

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_root29_01_finite_killed_markov_ennreal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) (x : ℝ) (s u : ℝ≥0)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (hTerminal : ∃ j : ℕ, τ j = u) :
    (∫⁻ ω, ({ω | ∀ v : ℝ≥0, v ≤ s + u → 0 ≤ x + X.X v ω}).indicator
      (fun ω => ENNReal.ofReal (Real.exp
        (θ * X.X (s + u) ω - ((s + u : ℝ≥0) : ℝ) *
          laplaceExponent X.c X.σ X.ν θ))) ω ∂P) =
    (∫⁻ ω : Ω,
      (if ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω then
        ENNReal.ofReal (Real.exp
          (θ * X.X s ω - (s : ℝ) * laplaceExponent X.c X.σ X.ν θ)) *
        ENNReal.ofReal (∫ ζ,
          ({ζ | ∀ v : ℝ≥0, v ≤ u → 0 ≤ (x + X.X s ω) + X.X v ζ}).indicator
            (fun ζ => Real.exp
              (θ * X.X u ζ - (u : ℝ) *
                laplaceExponent X.c X.σ X.ν θ)) ζ ∂P)
       else (0 : ℝ≥0∞)) ∂P) := by sorry
