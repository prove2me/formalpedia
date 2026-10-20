-- Prove2me | Theorems.Thm_DerivativeChainPrivate_exists_chain_cost_le_sqrt
-- name    : DerivativeChainPrivate.exists_chain_cost_le_sqrt
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-17T18:40:24.124226+00:00
-- url     : https://prove2.me/theorems/3dcae5e9-c83f-42bf-8264-8f0859236281
-- title:
--   Unanchored square-root derivative-chain baseline
-- statement:
--   Every list of n>0 complex roots in the closed unit disk defines a monic polynomial whose derivative tower admits a complete actual-root chain of Euclidean length
--
--   $$\ell\le\sqrt{n-1}.$$
--
--   The proof establishes the existence of the degree-one starting root. Repeated roots and the zero-cost degree-one case are included. This corollary remains degree-dependent.
-- source:
--   Derivative-zero chains: public formalization reference, R17, DerivativeChainPrivate.exists_chain_cost_le_sqrt. https://gist.github.com/Amal-David/d6612109c98595b12561cd638c60edf5/3883c57ddc7bf9d4c0e898c3d6bfd2ca0d7f9c95#file-notes-md

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

theorem DerivativeChainPrivate.exists_chain_cost_le_sqrt {n : ℕ} (hn : 0 < n) (a : Fin n → ℂ)
    (ha : ∀ i, ‖a i‖ ≤ 1) :
    ∃ z : Fin n → ℂ, IsChain a z ∧ chainCost z ≤ Real.sqrt ((n - 1 : ℕ) : ℝ) := by sorry
