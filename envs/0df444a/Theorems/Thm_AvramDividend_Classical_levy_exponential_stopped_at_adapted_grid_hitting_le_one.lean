-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_exponential_stopped_at_adapted_grid_hitting_le_one
-- name    : AvramDividend.Classical.levy_exponential_stopped_at_adapted_grid_hitting_le_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T22:57:37.255391+00:00
-- url     : https://prove2.me/theorems/01c11533-33e6-41a1-b210-70219a866777
-- title:
--   Optional stopping of the compensated Lévy exponential at an adapted grid hitting time
-- statement:
--   Fix a spectrally negative Lévy process, a nonnegative Laplace parameter, and any adapted real-valued process U observed on the integer-time grid. Stop the compensated exponential of the Lévy process at the first index in [0,N] where U is negative (or N if there is no such index). Its expected stopped value is at most one. Combine the proved exponential martingale and its unit initial expectation with natural-grid restriction and the proved bounded optional stopping inequality. No continuous-time stopping-time regularity is assumed.
-- source:
--   Proved Levy exponential martingale, compensated expectation one, natural martingale sampling, and bounded finite-grid optional-stopping lemma. Supporting bridge to Proposition 4(i), not a proof of its controlled-dividend stochastic-calculus leaves.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_exponential_stopped_at_adapted_grid_hitting_le_one
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {𝓖 : Filtration ℕ mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (h𝓖 : ∀ n : ℕ, 𝓖 n = 𝓕 (n : ℝ≥0))
    (θ : ℝ) (hθ : 0 ≤ θ)
    (U : ℕ → Ω → ℝ) (hU : Adapted 𝓖 U) (N : ℕ) :
    (∫ ω, stoppedValue
      (fun n : ℕ => fun ω =>
        Real.exp (θ * X.X (n : ℝ≥0) ω - ((n : ℝ≥0) : ℝ) * X.ψ θ))
      (fun ω => ((hittingBtwn U (Iio (0 : ℝ)) 0 N ω : ℕ) : WithTop ℕ)) ω ∂P) ≤
      1 := by sorry
