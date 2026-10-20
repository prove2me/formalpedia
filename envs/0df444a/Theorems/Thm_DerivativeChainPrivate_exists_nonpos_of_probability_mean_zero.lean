-- Prove2me | Theorems.Thm_DerivativeChainPrivate_exists_nonpos_of_probability_mean_zero
-- name    : DerivativeChainPrivate.exists_nonpos_of_probability_mean_zero
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-17T18:42:37.835531+00:00
-- url     : https://prove2.me/theorems/8f9888f8-2d42-48b9-b668-de1cfe7a4388
-- title:
--   Nonpositive value under a finite zero-mean probability law
-- statement:
--   Let I be a finite type, p_i nonnegative real weights with sum one, and f_i real values with weighted sum zero. Then
--
--   $$\exists i\in I,\quad f_i\le0.$$
--
--   The index type is initially permitted to be empty, but normalization rules that out. Zero individual weights are allowed. This finite selection lemma supports the energy-step argument.
-- source:
--   Derivative-zero chains: public formalization reference, R21, DerivativeChainPrivate.exists_nonpos_of_probability_mean_zero. https://gist.github.com/Amal-David/d6612109c98595b12561cd638c60edf5/3883c57ddc7bf9d4c0e898c3d6bfd2ca0d7f9c95#file-notes-md

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.GaussLucas
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
open scoped BigOperators Polynomial
set_option autoImplicit false
namespace DerivativeChainPrivate
end DerivativeChainPrivate
open DerivativeChainPrivate

theorem DerivativeChainPrivate.exists_nonpos_of_probability_mean_zero {ι : Type*} [Fintype ι]
    (p f : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) (hzero : ∑ i, p i * f i = 0) :
    ∃ i, f i ≤ 0 := by sorry
