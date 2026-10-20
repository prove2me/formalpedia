-- Prove2me | Theorems.Thm_DerivativeChainPrivate_exists_chain_cost_le
-- name    : DerivativeChainPrivate.exists_chain_cost_le
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-17T18:38:28.928224+00:00
-- url     : https://prove2.me/theorems/49bccd1a-0abd-4c39-b1aa-f92663275a9c
-- title:
--   Anchored complete derivative-chain baseline
-- statement:
--   Let n>0 and let all n complex root slots a_i lie in the closed unit disk. For every root u of their degree-one derivative row, a complete actual derivative-root chain z exists, starting at u, whose Euclidean length satisfies
--
--   $$\ell\le\sqrt{(n-1)(1-|u|^2)}.$$
--
--   Every nonconstant derivative row is retained. Repeated roots and n=1 are allowed. The starting point is specified as a row-one root; no separately assumed centroid formula or one-step transition hypothesis is used. The bound depends on degree and does not settle either unrestricted prize question.
-- source:
--   Derivative-zero chains: public formalization reference, R15, DerivativeChainPrivate.exists_chain_cost_le. https://gist.github.com/Amal-David/d6612109c98595b12561cd638c60edf5/3883c57ddc7bf9d4c0e898c3d6bfd2ca0d7f9c95#file-notes-md

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

theorem DerivativeChainPrivate.exists_chain_cost_le {n : ℕ} (hn : 0 < n) (a : Fin n → ℂ)
    (ha : ∀ i, ‖a i‖ ≤ 1) (u : ℂ) (hu : (row a 1).eval u = 0) :
    ∃ z : Fin n → ℂ, IsChain a z ∧ z ⟨0, hn⟩ = u ∧
      chainCost z ≤ Real.sqrt (((n - 1 : ℕ) : ℝ) * (1 - ‖u‖ ^ 2)) := by sorry
