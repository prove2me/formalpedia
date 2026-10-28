-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_neumann_finite_sum_additive_operator
-- name    : AvramDividend.Classical.causal_neumann_finite_sum_additive_operator
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T13:52:37.884511+00:00
-- url     : https://prove2.me/theorems/59bf8ad4-0f37-47da-b36c-1e3b7cea68e7
-- title:
--   Pointwise additive Volterra operators preserve finite Neumann sums
-- statement:
--   An operator T on real-valued functions that preserves zero and binary addition also preserves the finite Neumann partial sum of any sequence Q. This establishes precisely the hlinear hypothesis needed by the existing finite Neumann telescope, once the causal convolution operator has been proved additive.
-- source:
--   Induction over Finset.range; the operator is explicitly assumed additive and zero preserving.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset

theorem AvramDividend.Classical.causal_neumann_finite_sum_additive_operator
    (T : (ℝ → ℝ) → (ℝ → ℝ)) (Q : ℕ → ℝ → ℝ)
    (hzero : T 0 = 0)
    (hadd : ∀ f g : ℝ → ℝ, T (f + g) = T f + T g)
    (n : ℕ) :
    T (∑ i ∈ Finset.range (n + 1), Q i) =
      ∑ i ∈ Finset.range (n + 1), T (Q i) := by sorry
