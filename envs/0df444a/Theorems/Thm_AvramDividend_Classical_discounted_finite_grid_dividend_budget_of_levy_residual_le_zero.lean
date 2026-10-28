-- Prove2me | Theorems.Thm_AvramDividend_Classical_discounted_finite_grid_dividend_budget_of_levy_residual_le_zero
-- name    : AvramDividend.Classical.discounted_finite_grid_dividend_budget_of_levy_residual_le_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T07:59:39.33716+00:00
-- url     : https://prove2.me/theorems/9d929282-54e9-483d-a96b-fe20d9aec383
-- title:
--   Finite-grid stochastic dividend budget from nonpositive Lévy residual
-- statement:
--   Under the pathwise dividend secant inequality, the exact discounted ledger bounds the dividend stream by the initial verification value plus a signed Lévy residual minus the discounted terminal verification value. When the finite-grid residual is nonpositive and the terminal verification value is nonnegative, discounted dividends cannot exceed the initial verification value. This finite-grid closing lemma leaves only probabilistic residual supermartingale control and mesh convergence to be established for stochastic verification.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), finite-grid stopped discounted verification inequality.

import Mathlib.Data.Finset.Range
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_discounted_finite_grid_levy_dividend_secant_ledger

open Finset
open AvramDividend.Classical

theorem AvramDividend.Classical.discounted_finite_grid_dividend_budget_of_levy_residual_le_zero
    (w : ℝ → ℝ) (u preDividend cash : ℕ → ℝ)
    (s : ℕ → ℝ) (q : ℝ) (hs0 : s 0 = 0)
    (hCash : ∀ k : ℕ, cash k ≤ w (preDividend k) - w (u (k + 1)))
    (n : ℕ)
    (hResidual : (∑ k ∈ Finset.range n,
      (Real.exp (-(q * s (k + 1))) * w (preDividend k) -
        Real.exp (-(q * s k)) * w (u k))) ≤ 0)
    (hTerminal : 0 ≤ w (u n)) :
    (∑ k ∈ Finset.range n, Real.exp (-(q * s (k + 1))) * cash k) ≤
      w (u 0) := by sorry
