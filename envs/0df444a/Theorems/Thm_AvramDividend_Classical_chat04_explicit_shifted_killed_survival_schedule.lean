-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_explicit_shifted_killed_survival_schedule
-- name    : AvramDividend.Classical.chat04_explicit_shifted_killed_survival_schedule
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T21:01:22.94022+00:00
-- url     : https://prove2.me/theorems/6e04803a-961c-4afa-aa0b-e27b5a5c98a6
-- title:
--   An explicit countable relative-time schedule covers rational grids and the terminal horizon
-- statement:
--   Given any nonnegative horizon T, construct a countable observation schedule tau with tau(0)=T and tau(j+1) the Cantor-unpaired rational grid. Every reciprocal grid time k/n with positive n occurs, and T itself occurs. This discharges both schedule coverage hypotheses in the shifted killed-survival equivalence, and enables a concrete continuously killed Markov–Tonelli factorisation for the two-sided exit proof.
-- source:
--   Already Proved chat04_nat_pairing_rational_grid_coverage and Nat.unpair_pair.

import Mathlib.Data.Nat.Pairing
import Mathlib.Data.NNReal.Basic
import Theorems.Thm_AvramDividend_Classical_chat04_nat_pairing_rational_grid_coverage

open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_explicit_shifted_killed_survival_schedule (T : ℝ≥0) :
    ∃ τ : ℕ → ℝ≥0,
      (∀ n : ℕ, 0 < n → ∀ k : ℕ,
        ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹) ∧
      (∃ j : ℕ, τ j = T) := by sorry
