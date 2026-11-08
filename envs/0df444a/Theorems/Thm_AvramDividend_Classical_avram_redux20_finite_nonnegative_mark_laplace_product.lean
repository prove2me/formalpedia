-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_redux20_finite_nonnegative_mark_laplace_product
-- name    : AvramDividend.Classical.avram_redux20_finite_nonnegative_mark_laplace_product
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T08:59:47.997681+00:00
-- url     : https://prove2.me/theorems/ce2ad556-b0dd-4c78-9607-9c02606235dc
-- title:
--   Finite nonnegative extended-real marked Laplace weight is a real exponential product
-- statement:
--   For a finite set of actual marked jumps with nonnegative magnitude losses, the real Laplace factor of their finite extended-real total equals the product of the individual real exponential factors. This is the deterministic expression used for finite Poisson mark bins after specialising the original intrinsic marked-jump integral.
-- source:
--   Use ENNReal.toReal_sum on a finite family of finite terms, each ENNReal.toReal_ofReal at a nonnegative real, the finite-sum negation identity, and the pinned Real.exp_sum lemma.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_redux20_finite_nonnegative_mark_laplace_product
    {α : Type*} (S : Finset α) (a : α → ℝ)
    (ha : ∀ u ∈ S, 0 ≤ a u) :
    Real.exp (-(∑ u ∈ S, ENNReal.ofReal (a u)).toReal) =
      ∏ u ∈ S, Real.exp (-(a u)) := by sorry
