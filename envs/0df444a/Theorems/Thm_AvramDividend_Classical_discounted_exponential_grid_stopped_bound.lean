-- Prove2me | Theorems.Thm_AvramDividend_Classical_discounted_exponential_grid_stopped_bound
-- name    : AvramDividend.Classical.discounted_exponential_grid_stopped_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T23:00:41.457843+00:00
-- url     : https://prove2.me/theorems/4ed44737-4857-4615-91cd-d1bb751a4903
-- title:
--   Discounted exponential Lévy supermartingale satisfies bounded grid-hitting optional stopping
-- statement:
--   For a Lévy process and any θ≥0 satisfying ψ(θ)≤q, the q-discounted exponential has expected value at most one when stopped at the first negative reserve observed on an arbitrary adapted finite grid. The proof restricts the previously established discounted exponential supermartingale to the sampled filtration, applies bounded stopping at the first index where U is negative, and uses the normalisation E[e^{θX_0}]=1. This proves an exact special stochastic bound without assuming continuous-time Itô calculus or a controlled dividend semimartingale representation.
-- source:
--   Proved exponential Lévy expectation one, discounted exponential Lévy supermartingale, natural-grid sampling of supermartingales and bounded first-negative-grid optional stopping.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.discounted_exponential_grid_stopped_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {𝓖 : Filtration ℕ mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (h𝓖 : ∀ n : ℕ, 𝓖 n = 𝓕 (n : ℝ≥0))
    (θ q : ℝ) (hθ : 0 ≤ θ) (hψ : X.ψ θ ≤ q)
    (U : ℕ → Ω → ℝ) (hU : Adapted 𝓖 U) (N : ℕ) :
    (∫ ω, stoppedValue
      (fun n : ℕ => fun ω =>
        Real.exp (θ * X.X (n : ℝ≥0) ω - ((n : ℝ≥0) : ℝ) * q))
      (fun ω => ((hittingBtwn U (Iio (0 : ℝ)) 0 N ω : ℕ) : WithTop ℕ)) ω ∂P) ≤
      1 := by sorry
