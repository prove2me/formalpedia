-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_increment_condExp_general_reserve_lipschitz_measurable
-- name    : AvramDividend.Classical.levy_increment_condExp_general_reserve_lipschitz_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T20:34:39.990205+00:00
-- url     : https://prove2.me/theorems/a7cd0496-c4a3-4f24-835b-ac32e0f82e5c
-- title:
--   Lipschitz random-reserve conditional Lévy Markov identity with automatic measurability and conditional integrability
-- statement:
--   For a spectrally negative Lévy process, a Lipschitz payoff with integrable deterministic transition, adapted simple reserve approximations to a measurable random reserve, and explicit payoff/integrable transition differences and vanishing scaled L1 state-approximation error, the conditional Lévy Markov identity holds almost everywhere. Unlike the preceding Lipschitz transfer theorem, strong measurability of conditional expectation and transition terms, and integrability of the conditional expectation differences, are derived automatically. Use the generic conditional-expectation side-condition theorem, transition strong-measurability lemma, and already Proved Lipschitz general-reserve Markov theorem. Remaining obligations are existence of adapted simple approximants, their scaled L1 convergence, and integrability of the random payoff/transition differences; no stopped generator verification is asserted.
-- source:
--   Proved general-reserve Lipschitz Markov target 6a0881ef-ae88-4638-9bff-45e826da51a8; two pending child publications for conditional-expectation side conditions and random-reserve transition strong measurability.

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_condExp_pair_stronglyMeasurable_integrable_difference
import Theorems.Thm_AvramDividend_Classical_levy_transition_random_reserve_stronglyMeasurable
import Theorems.Thm_AvramDividend_Classical_levy_increment_condExp_general_reserve_lipschitz

open Filter MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_increment_condExp_general_reserve_lipschitz_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (f : ℝ → ℝ) (hf : Measurable f) (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |f u - f v| ≤ L * |u - v|)
    (hInt : ∀ x : ℝ, Integrable
      (fun η => f (x + X.X (t - s) η)) P)
    (Sn : ℕ → SimpleFunc Ω ℝ) (Z : Ω → ℝ)
    (hSn : ∀ n, Measurable[𝓕 s] (Sn n : Ω → ℝ))
    (hZMeas : Measurable Z)
    (hZ : Integrable (fun ω =>
      f (Z ω + (X.X t ω - X.X s ω))) P)
    (hZn : ∀ n, Integrable (fun ω =>
      f (Sn n ω + (X.X t ω - X.X s ω))) P)
    (hTDiff : ∀ n, Integrable (fun ω =>
      (∫ η, f (Sn n ω + X.X (t - s) η) ∂P) -
      (∫ η, f (Z ω + X.X (t - s) η) ∂P)) P)
    (hDom : ∀ n, Integrable
      (fun ω => L * |Sn n ω - Z ω|) P)
    (hlim : Tendsto (fun n : ℕ =>
      ∫ ω, L * |Sn n ω - Z ω| ∂P)
      atTop (nhds 0)) :
    P[(fun η => f (Z η + (X.X t η - X.X s η))) | 𝓕 s] =ᵐ[P]
      (fun ω => ∫ η, f (Z ω + X.X (t - s) η) ∂P) := by sorry
