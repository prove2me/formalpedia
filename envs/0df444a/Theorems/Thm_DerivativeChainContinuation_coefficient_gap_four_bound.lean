-- Prove2me | Theorems.Thm_DerivativeChainContinuation_coefficient_gap_four_bound
-- name    : DerivativeChainContinuation.coefficient_gap_four_bound
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T21:11:50.422588+00:00
-- url     : https://prove2.me/theorems/28cd11b8-3f92-46d6-9d1a-da71b48f5d01
-- title:
--   A coefficient gap with tail length at most fifteen gives a four-bound
-- statement:
--   Let $p\in\mathbb C[X]$ be monic of degree $n$ with centroid $u$. Suppose $1\le h\le15$, $h\le k\le n-2$, and $p(X+u)=X^n+AX^k+Q(X)$ with $A\in\mathbb C$ and $\deg Q<h$. If every root of $p$ lies in the closed unit disk, there is an actual derivative chain starting at $u$ satisfying
--
--   $$L(z)\le4.$$
--
--   For a finite complex path $z_0,\ldots,z_{N-1}$, write $L(z)=\sum_{i=0}^{N-2}|z_{i+1}-z_i|$. An actual derivative chain for a degree-$N$ polynomial $p$ satisfies $p^{(N-i-1)}(z_i)=0$ for every $0\le i<N$. The restriction on $h$ is part of the theorem.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/CoefficientGapFour.lean#L6-L25

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CenteredSource
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

theorem DerivativeChainContinuation.coefficient_gap_four_bound (p : Polynomial ℂ) (hp : p.Monic) (n h k : ℕ)
    (hn : p.natDegree=n) (hh : 1 ≤ h) (hh15 : h ≤ 15) (hhk : h ≤ k) (hk : k ≤ n-2)
    (A : ℂ) (Q : Polynomial ℂ) (hQ : Q.natDegree < h)
    (hgap : centeredSource p=X^n+C A*X^k+Q)
    (hbound : ∀ z : ℂ, p.eval z=0 → ‖z‖ ≤ 1) :
    ∃ z : Fin n → ℂ,
      (∀ i, (derivative^[n-(i.val+1)] p).eval (z i)=0) ∧
      z ⟨0,by omega⟩=rootCentroid p ∧ chainCost z ≤ 4 := by sorry
