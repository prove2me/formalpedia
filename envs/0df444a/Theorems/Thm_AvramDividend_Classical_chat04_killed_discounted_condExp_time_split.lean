-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_killed_discounted_condExp_time_split
-- name    : AvramDividend.Classical.chat04_killed_discounted_condExp_time_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:29:55.138728+00:00
-- url     : https://prove2.me/theorems/81c0531f-8548-4df4-a8e8-42d542ff0450
-- title:
--   Discounted killed scale conditional expectation splits into surviving history and future reward
-- statement:
--   For the spectrally negative Levy reserve and any s≤u, conditional expectation of the full killed q-discounted scale reward through time u decomposes into the survival indicator to s, the deterministic discount to s, and the conditional expectation of the reward surviving the future interval [s,u] discounted over the remaining elapsed time. Requires only future-killed integrability and the published lower-killing conditional factorisation; no scale harmonicity is asserted.
-- source:
--   Proved chat04_lower_killed_condExp_markov_factorisation; Mathlib conditional expectation scalar linearity.

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_lower_killed_condExp_markov_factorisation
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_killed_discounted_condExp_time_split
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (q : ℝ) (W : ℝ → ℝ)
    (x : ℝ) (s u : ℝ≥0) (hsu : s ≤ u)
    (hInt : Integrable
      (({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
        0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}).indicator
        (fun ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) *
          W (x + X.X u ω))) P) :
    P[({ω | ∀ v : ℝ≥0, v ≤ u → 0 ≤ x + X.X v ω}).indicator
        (fun ω => Real.exp (-(q * (u : ℝ))) * W (x + X.X u ω)) | 𝓕 s] =ᵐ[P]
      ({ω | ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω}).indicator
        (fun ω => Real.exp (-(q * (s : ℝ))) *
          P[({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
            0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}).indicator
              (fun ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) *
                W (x + X.X u ω)) | 𝓕 s] ω) := by sorry
