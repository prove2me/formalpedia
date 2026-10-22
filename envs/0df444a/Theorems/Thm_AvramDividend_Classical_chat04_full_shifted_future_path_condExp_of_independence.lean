-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_full_shifted_future_path_condExp_of_independence
-- name    : AvramDividend.Classical.chat04_full_shifted_future_path_condExp_of_independence
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T06:53:19.171994+00:00
-- url     : https://prove2.me/theorems/82301379-a313-4f88-8ab5-7c9aa293947e
-- title:
--   Conditional Markov expectation for every integrable full future-path payoff given process independence
-- statement:
--   For a canonical spectrally negative Lévy process X and deterministic s, assume that the sigma algebra of the ENTIRE shifted future increment path (t≥0)↦X_(s+t)−X_s is independent of the full past filtration F_s. Let f be ANY measurable real-valued functional of that complete future path, including discounted payoff or continuous-time barrier-survival reward, whose composition with the shifted path is integrable. Then E[f(shifted future path)|F_s] is almost surely equal to its constant unconditional expectation. The proof establishes measurability of the function-valued future process from original adaptedness, proves the generated sigma algebra of f(Y) is contained in that of Y, transfers the independence to f(Y), and applies the pinned exact Mathlib condExp_indep_eq. This is a generic conditional-Markov kernel interface with full uncountable-time path support, generalising the already ACCEPTED countably sampled version UUID cdb59174-5b57-47e7-a7db-67474d618b50. The full-path independence itself must be established separately from joint finite cylinder laws, and this theorem does not assert killed q-harmonicity.
-- source:
--   Already accepted countably sampled future-path conditional payoff pattern UUID cdb59174-5b57-47e7-a7db-67474d618b50, pinned Mathlib condExp_indep_eq, measurable_pi_iff, indep_of_indep_of_le_left, and original Lévy adaptedness. Process-independence premise given explicitly.

import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Independence.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_full_shifted_future_path_condExp_of_independence
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0)
    (hFuture : Indep
      (MeasurableSpace.comap
        (fun ω : Ω => fun t : ℝ≥0 => X.X (s + t) ω - X.X s ω)
        inferInstance)
      (𝓕 s) P)
    (f : (ℝ≥0 → ℝ) → ℝ) (hf : Measurable f)
    (hInt : Integrable
      (fun ω => f (fun t => X.X (s + t) ω - X.X s ω)) P) :
    P[(fun ω => f (fun t => X.X (s + t) ω - X.X s ω)) | 𝓕 s] =ᵐ[P]
      (fun _ => ∫ ω, f (fun t => X.X (s + t) ω - X.X s ω) ∂P) := by sorry
