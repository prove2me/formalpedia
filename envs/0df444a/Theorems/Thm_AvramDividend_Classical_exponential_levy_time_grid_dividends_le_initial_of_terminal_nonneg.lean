-- Prove2me | Theorems.Thm_AvramDividend_Classical_exponential_levy_time_grid_dividends_le_initial_of_terminal_nonneg
-- name    : AvramDividend.Classical.exponential_levy_time_grid_dividends_le_initial_of_terminal_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T18:48:21.315991+00:00
-- url     : https://prove2.me/theorems/4913812f-1e62-4c98-b705-9347ced4d9e5
-- title:
--   Expected discounted grid dividends bounded on a sampled continuous-time Lévy filtration
-- statement:
--   In a probability space with a continuous-time filtration 𝓕 indexed by nonnegative reals, sample a monotone grid of nonnegative times s_k starting at zero. Suppose the sampled reserve process begins at deterministic x, the discounted grid cash and candidate values are integrable, each conditional one-step discounted dividend inequality holds with conditioning on the original filtration 𝓕_(s_k), and the expected terminal candidate value is nonnegative. Then the expected sum of discounted dividend payments on the grid is at most w(x). Construct the sigma-finite natural-number filtration by sampling 𝓕 at s_k using the independently Proved sampled_levy_filtration_exists_of_monotone_grid, then instantiate the independently Proved exponential_grid_expected_dividends_le_initial_of_terminal_nonneg. This directly connects the Lévy time index used by the proved semigroup one-step estimate to the finite-grid dividend budget in the capped BV/UV branch. The remaining unresolved step is the stopped Lévy calculus and approximation for continuous dividends.

import Mathlib.Probability.Process.Filtration
import Theorems.Thm_AvramDividend_Classical_sampled_levy_filtration_exists_of_monotone_grid
import Theorems.Thm_AvramDividend_Classical_exponential_grid_expected_dividends_le_initial_of_terminal_nonneg

open MeasureTheory ProbabilityTheory
open scoped NNReal

theorem AvramDividend.Classical.exponential_levy_time_grid_dividends_le_initial_of_terminal_nonneg
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (s : ℕ → ℝ≥0) (hs : Monotone s) (hs0 : s 0 = 0)
    (u a : ℕ → Ω → ℝ) (w : ℝ → ℝ) (q x : ℝ)
    (hu0 : ∀ᵐ ω ∂P, u 0 ω = x)
    (hCashI : ∀ k,
      Integrable (fun ω => Real.exp (-(q * (s k : ℝ))) * a k ω) P)
    (hVI : ∀ k,
      Integrable (fun ω => Real.exp (-(q * (s k : ℝ))) * w (u k ω)) P)
    (hstep : ∀ k : ℕ, ∀ᵐ ω ∂P,
      a k ω + Real.exp (-(q * ((s (k + 1) : ℝ) - (s k : ℝ)))) *
        (P[(fun η => w (u (k + 1) η)) | 𝓕 (s k)]) ω ≤ w (u k ω))
    (n : ℕ)
    (hterminal : 0 ≤
      ∫ ω, Real.exp (-(q * (s n : ℝ))) * w (u n ω) ∂P) :
    (∑ k ∈ Finset.range n,
      ∫ ω, Real.exp (-(q * (s k : ℝ))) * a k ω ∂P) ≤ w x := by sorry
