-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger82_discounted_secant_ledger_with_cell_errors
-- name    : AvramDividend.Classical.avram_gledger82_discounted_secant_ledger_with_cell_errors
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T09:01:29.359025+00:00
-- url     : https://prove2.me/theorems/23e21299-3eb4-4025-8b63-88749ce9941a
-- title:
--   Discounted finite-grid dividend secant ledger with explicitly charged per-cell errors
-- statement:
--   The error-tolerant form of the already-Proved discounted finite-grid dividend secant ledger. Any excess in a one-cell dividend inequality is charged at that cell's right-endpoint discounted weight. The conclusion is a finite arithmetic inequality and does not assume stochastic properties or a global reward derivative bound. This is the summation tool required to assemble gledger81's original pathwise Stieltjes payment-cell inequalities without losing terminal atoms.
-- source:
--   Root-connected gledger81 16e988d7 strict stopped dividend-contact mesh correction: every physical cell uses a proved right-endpoint/strict crossing secant with a time-discount error. Exact finite telescoping with errors is extracted from Proved eadfa500, rather than a new cash/residual sketch.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_discounted_finite_grid_levy_dividend_secant_ledger
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_gledger82_discounted_secant_ledger_with_cell_errors
    (w : ℝ → ℝ) (u preDividend cash err : ℕ → ℝ)
    (s : ℕ → ℝ) (q : ℝ) (hs0 : s 0 = 0)
    (hCash : ∀ k : ℕ, cash k ≤ w (preDividend k) - w (u (k + 1)) + err k)
    (n : ℕ) :
    (∑ k ∈ Finset.range n, Real.exp (-(q * s (k + 1))) * cash k) +
        Real.exp (-(q * s n)) * w (u n) ≤
      w (u 0) +
        ∑ k ∈ Finset.range n,
          (Real.exp (-(q * s (k + 1))) * w (preDividend k) -
            Real.exp (-(q * s k)) * w (u k)) +
      ∑ k ∈ Finset.range n, Real.exp (-(q * s (k + 1))) * err k := by sorry
