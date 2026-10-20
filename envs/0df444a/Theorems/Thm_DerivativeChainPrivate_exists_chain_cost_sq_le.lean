-- Prove2me | Theorems.Thm_DerivativeChainPrivate_exists_chain_cost_sq_le
-- name    : DerivativeChainPrivate.exists_chain_cost_sq_le
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-17T18:40:58.035594+00:00
-- url     : https://prove2.me/theorems/a064904b-8320-4541-86ef-f4d78cd2d7c6
-- title:
--   Squared complete derivative-chain baseline
-- statement:
--   Let n>0 and let the n complex root slots a_i lie in the closed unit disk. For any root u of their degree-one derivative row there exists a complete actual derivative-root chain z starting at u, with total Euclidean chain length ell satisfying
--
--   $$\ell^2\le(n-1)(1-|u|^2).$$
--
--   Multiplicity is preserved in the source polynomial. Degree one has zero edges. This is a degree-dependent baseline, not a degree-independent constant bound.
-- source:
--   Derivative-zero chains: public formalization reference, R18, DerivativeChainPrivate.exists_chain_cost_sq_le. https://gist.github.com/Amal-David/d6612109c98595b12561cd638c60edf5/3883c57ddc7bf9d4c0e898c3d6bfd2ca0d7f9c95#file-notes-md

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

theorem DerivativeChainPrivate.exists_chain_cost_sq_le {n : ℕ} (hn : 0 < n) (a : Fin n → ℂ)
    (ha : ∀ i, ‖a i‖ ≤ 1) (u : ℂ) (hu : (row a 1).eval u = 0) :
    ∃ z : Fin n → ℂ, IsChain a z ∧ z ⟨0, hn⟩ = u ∧
      chainCost z ^ 2 ≤ ((n - 1 : ℕ) : ℝ) * (1 - ‖u‖ ^ 2) := by sorry
