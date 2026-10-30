-- Prove2me | Theorems.Thm_DerivativeChainContinuation_at_most_two_centered_modes_unit_disk
-- name    : DerivativeChainContinuation.at_most_two_centered_modes_unit_disk
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T21:06:53.407645+00:00
-- url     : https://prove2.me/theorems/e1de260e-ab9a-4971-a6bb-209922d2f2a3
-- title:
--   Two centered modes in the unit disk give a one-plus-root-two bound
-- statement:
--   Let $p\in\mathbb C[X]$ be monic of positive degree $n$. Suppose all roots lie in the closed unit disk and at most two centered modes indexed by $2\le j\le n$ are nonzero. There is an actual derivative chain starting at the root centroid with
--
--   $$L(z)\le1+\sqrt2.$$
--
--   A centered mode indexed by $j$ is the coefficient of $X^{n-j}$ after translation by the centroid. For a finite complex path $z_0,\ldots,z_{N-1}$, write $L(z)=\sum_{i=0}^{N-2}|z_{i+1}-z_i|$. An actual derivative chain for a degree-$N$ polynomial $p$ satisfies $p^{(N-i-1)}(z_i)=0$ for every $0\le i<N$.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/SparseCorollaries.lean#L36-L49

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CenteredSource
import Definitions.Def_DerivativeChainContinuation_TwoModeChain
import Definitions.Def_DerivativeChainPrivate_foundations
import Definitions.Def_DerivativeChain_root_probability
open DerivativeChain DerivativeChainPrivate
open Polynomial
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate







end DerivativeChainContinuation

theorem DerivativeChainContinuation.at_most_two_centered_modes_unit_disk (p : Polynomial ℂ) (hp : p.Monic)
    (n : ℕ) (hn : p.natDegree=n) (hnpos : 0 < n)
    (hmodes : (centeredModeSupport p).card ≤ 2)
    (hbound : ∀ z : ℂ, p.eval z=0 → ‖z‖ ≤ 1) :
    ∃ z : Fin n → ℂ,
      (∀ i, (derivative^[n-(i.val+1)] p).eval (z i)=0) ∧
      z ⟨0,hnpos⟩=rootCentroid p ∧ chainCost z ≤ 1+Real.sqrt 2 := by sorry
