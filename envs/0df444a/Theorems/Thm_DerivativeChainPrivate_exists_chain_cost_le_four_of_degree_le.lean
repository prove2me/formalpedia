-- Prove2me | Theorems.Thm_DerivativeChainPrivate_exists_chain_cost_le_four_of_degree_le
-- name    : DerivativeChainPrivate.exists_chain_cost_le_four_of_degree_le
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-17T18:39:11.643984+00:00
-- url     : https://prove2.me/theorems/d9946059-3fb3-412e-a8b5-2e850c80de7d
-- title:
--   Derivative-chain bound four for degrees through seventeen
-- statement:
--   For every positive degree n<=17 and every list of n complex roots in the closed unit disk, the associated monic polynomial has a complete derivative-root chain with
--
--   $$\ell\le4.$$
--
--   This is only the finite-degree corollary of the square-root baseline. It is not the all-degree bound four.
-- source:
--   Derivative-zero chains: public formalization reference, R16, DerivativeChainPrivate.exists_chain_cost_le_four_of_degree_le. https://gist.github.com/Amal-David/d6612109c98595b12561cd638c60edf5/3883c57ddc7bf9d4c0e898c3d6bfd2ca0d7f9c95#file-notes-md

import Definitions.Def_DerivativeChainPrivate_foundations
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

theorem DerivativeChainPrivate.exists_chain_cost_le_four_of_degree_le {n : ℕ} (hn : 0 < n) (hn17 : n ≤ 17)
    (a : Fin n → ℂ) (ha : ∀ i, ‖a i‖ ≤ 1) :
    ∃ z : Fin n → ℂ, IsChain a z ∧ chainCost z ≤ 4 := by sorry
