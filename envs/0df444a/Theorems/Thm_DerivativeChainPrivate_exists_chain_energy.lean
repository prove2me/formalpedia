-- Prove2me | Theorems.Thm_DerivativeChainPrivate_exists_chain_energy
-- name    : DerivativeChainPrivate.exists_chain_energy
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-17T18:41:37.761409+00:00
-- url     : https://prove2.me/theorems/840eb3d1-e198-4c76-b7ac-68d3e95f084b
-- title:
--   Complete derivative-chain energy telescope
-- statement:
--   For n>0, let a be any list of n complex root slots, and let u be any zero of the degree-one row of their monic product polynomial. There is a chain selecting an actual zero of every row from degree one through n, starting at u, with
--
--   $$\sum_{i=0}^{n-2}|z_{i+1}-z_i|^2\le |z_{n-1}|^2-|u|^2.$$
--
--   No unit-disk assumption or unproved transition hypothesis remains. Repeated roots and n=1 are included.
-- source:
--   Derivative-zero chains: public formalization reference, R19, DerivativeChainPrivate.exists_chain_energy. https://gist.github.com/Amal-David/d6612109c98595b12561cd638c60edf5/3883c57ddc7bf9d4c0e898c3d6bfd2ca0d7f9c95#file-notes-md

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

theorem DerivativeChainPrivate.exists_chain_energy {n : ℕ} (hn : 0 < n) (a : Fin n → ℂ) (u : ℂ)
    (hu : (row a 1).eval u = 0) :
    ∃ z : Fin n → ℂ, IsChain a z ∧ z ⟨0, hn⟩ = u ∧
      (∑ i : Fin (n - 1),
        ‖z ⟨i.val + 1, by omega⟩ - z ⟨i.val, by omega⟩‖ ^ 2) ≤
        ‖z ⟨n - 1, by omega⟩‖ ^ 2 - ‖u‖ ^ 2 := by sorry
