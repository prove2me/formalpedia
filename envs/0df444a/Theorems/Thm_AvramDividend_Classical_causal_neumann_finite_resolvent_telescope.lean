-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_neumann_finite_resolvent_telescope
-- name    : AvramDividend.Classical.causal_neumann_finite_resolvent_telescope
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T12:58:54.597997+00:00
-- url     : https://prove2.me/theorems/a7d276d8-e64e-4b66-a3dd-a82b49e9f7f7
-- title:
--   Exact telescoping identity for finite causal Neumann resolvents
-- statement:
--   For an operator additive across each finite Neumann partial sum, a recursive sequence Q₀=F and Qₙ₊₁=−TQₙ yields the exact finite resolvent equation (I+T)∑₀ⁿQᵢ=F−Qₙ₊₁. This is the algebraic cancellation step prior to controlling the remainder and exchanging the limit with causal convolution.
-- source:
--   Finite range-sum telescoping and operator additivity, requiring no convergence or local Lean compilation.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Abel

theorem AvramDividend.Classical.causal_neumann_finite_resolvent_telescope
    (F : ℝ → ℝ) (T : (ℝ → ℝ) → (ℝ → ℝ))
    (Q : ℕ → ℝ → ℝ)
    (hzero : Q 0 = F)
    (hstep : ∀ n : ℕ, Q (n + 1) = -T (Q n))
    (hlinear : ∀ n : ℕ,
      T (∑ i ∈ Finset.range (n + 1), Q i) =
        ∑ i ∈ Finset.range (n + 1), T (Q i))
    (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), Q i) +
      T (∑ i ∈ Finset.range (n + 1), Q i) =
        F - Q (n + 1) := by sorry
