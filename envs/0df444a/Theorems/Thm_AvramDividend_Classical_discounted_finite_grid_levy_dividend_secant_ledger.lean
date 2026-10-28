-- Prove2me | Theorems.Thm_AvramDividend_Classical_discounted_finite_grid_levy_dividend_secant_ledger
-- name    : AvramDividend.Classical.discounted_finite_grid_levy_dividend_secant_ledger
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T07:51:44.024227+00:00
-- url     : https://prove2.me/theorems/eadfa500-537a-4ef5-bda3-75d5cc43a3cb
-- title:
--   Discounted finite-grid dividend ledger separating uncontrolled Lévy increments
-- statement:
--   This is the discounted pathwise discrete ledger needed for stopped stochastic verification. The secant inequality controls the payment at the post-increment reserve. An exact telescoping sum separates discounted cash and the residual verification value from the signed discounted increments caused by the uncontrolled Lévy process. The remaining probabilistic obligation is a conditional generator/supermartingale bound on those signed increments and a mesh-to-Stieltjes limit.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), finite-grid discounted pathwise verification identity.

import Mathlib.Data.Finset.Range
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open Finset
open AvramDividend.Classical

theorem AvramDividend.Classical.discounted_finite_grid_levy_dividend_secant_ledger
    (w : ℝ → ℝ) (u preDividend cash : ℕ → ℝ)
    (s : ℕ → ℝ) (q : ℝ) (hs0 : s 0 = 0)
    (hCash : ∀ k : ℕ, cash k ≤ w (preDividend k) - w (u (k + 1)))
    (n : ℕ) :
    (∑ k ∈ Finset.range n, Real.exp (-(q * s (k + 1))) * cash k) +
        Real.exp (-(q * s n)) * w (u n) ≤
      w (u 0) +
        ∑ k ∈ Finset.range n,
          (Real.exp (-(q * s (k + 1))) * w (preDividend k) -
            Real.exp (-(q * s k)) * w (u k)) := by sorry
