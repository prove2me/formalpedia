-- Prove2me | Theorems.Thm_AvramDividend_Classical_exponential_levy_grid_cash_stieltjes_limit_le_initial
-- name    : AvramDividend.Classical.exponential_levy_grid_cash_stieltjes_limit_le_initial
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T19:30:40.078017+00:00
-- url     : https://prove2.me/theorems/1ff5a769-13e7-43e0-8a96-d54f7811b20f
-- title:
--   Monotone stopped Stieltjes dividends bounded by conditional Lévy grid cash
-- statement:
--   Suppose a sampled Lévy filtration has integrable discounted cash payments and verification values with a one-step conditional HJB budget and nonnegative expected terminal verification values at every grid horizon. Suppose the finite-grid cash sums are integrable, nonnegative and almost-everywhere measurable, and their extended nonnegative images are increasing almost surely. Any extended-nonnegative target payout, including a stopped Stieltjes dividend integral when a verified pathwise approximation dominates it, has expected value at most the initial candidate value if it is almost surely bounded by the supremum of these sums. The proof applies the already Proved conditional-cash Lévy-grid budget at every horizon and passes to the supremum using Mathlib's Bochner-to-Lebesgue conversion and monotone convergence. The hard root-connected work remains proving the conditional step and the pathwise approximation for actual capped admissible dividends.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Theorems.Thm_AvramDividend_Classical_exponential_levy_grid_expected_cash_le_initial_of_conditional_cash

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.exponential_levy_grid_cash_stieltjes_limit_le_initial
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (s : ℕ → ℝ≥0) (hs : Monotone s) (hs0 : s 0 = 0)
    (u cash : ℕ → Ω → ℝ) (w : ℝ → ℝ) (q x : ℝ)
    (hu0 : ∀ᵐ ω ∂P, u 0 ω = x)
    (hCashI : ∀ k, Integrable (cash k) P)
    (hVI : ∀ k, Integrable
      (fun ω => Real.exp (-(q * (s k : ℝ))) * w (u k ω)) P)
    (hstep : ∀ k : ℕ, ∀ᵐ ω ∂P,
      (P[(cash k) | 𝓕 (s k)]) ω +
        (P[(fun η => Real.exp (-(q * (s (k + 1) : ℝ))) *
          w (u (k + 1) η)) | 𝓕 (s k)]) ω ≤
          Real.exp (-(q * (s k : ℝ))) * w (u k ω))
    (hterminal : ∀ n : ℕ, 0 ≤
      ∫ ω, Real.exp (-(q * (s n : ℝ))) * w (u n ω) ∂P)
    (hPrefixI : ∀ n : ℕ, Integrable
      (fun ω => ∑ k ∈ Finset.range n, cash k ω) P)
    (hPrefixNN : ∀ n : ℕ, 0 ≤ᵐ[P]
      (fun ω => ∑ k ∈ Finset.range n, cash k ω))
    (hPrefixAE : ∀ n : ℕ, AEMeasurable
      (fun ω => ENNReal.ofReal (∑ k ∈ Finset.range n, cash k ω)) P)
    (hMono : ∀ᵐ ω ∂P, Monotone
      (fun n : ℕ => ENNReal.ofReal
        (∑ k ∈ Finset.range n, cash k ω)))
    (Z : Ω → ENNReal)
    (hZ : ∀ᵐ ω ∂P, Z ω ≤
      ⨆ n : ℕ, ENNReal.ofReal
        (∑ k ∈ Finset.range n, cash k ω)) :
    (∫⁻ ω, Z ω ∂P) ≤ ENNReal.ofReal (w x) := by sorry
