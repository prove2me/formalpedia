-- Prove2me | Theorems.Thm_AvramDividend_Classical_finite_grid_levy_dividend_secant_ledger
-- name    : AvramDividend.Classical.finite_grid_levy_dividend_secant_ledger
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T07:51:43.741979+00:00
-- url     : https://prove2.me/theorems/e6a4939a-fcff-48ef-aafe-c6ea506f0878
-- title:
--   Finite-grid pathwise dividend ledger with separate Lévy increments
-- statement:
--   This pathwise finite-grid ledger separates the effect of each Lévy increment from the subsequent dividend payment. The cash-flow secant inequality bounds cash at step k by the decrease in the verification function when control acts, while the uncontrolled increment contributes w(preDividend k)-w(u k). Induction telescopes the verification value. To obtain a stochastic HJB bound, a separate generator/martingale estimate must still control the expected increment sum. This theorem makes no claim about that missing step.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), elementary algebraic control part of verification.

import Mathlib.Data.Finset.Range
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open Finset
open AvramDividend.Classical

theorem AvramDividend.Classical.finite_grid_levy_dividend_secant_ledger
    (w : ℝ → ℝ) (u preDividend cash : ℕ → ℝ)
    (hCash : ∀ k : ℕ, cash k ≤ w (preDividend k) - w (u (k + 1)))
    (n : ℕ) :
    (∑ k ∈ Finset.range n, cash k) + w (u n) ≤
      w (u 0) + ∑ k ∈ Finset.range n, (w (preDividend k) - w (u k)) := by sorry
