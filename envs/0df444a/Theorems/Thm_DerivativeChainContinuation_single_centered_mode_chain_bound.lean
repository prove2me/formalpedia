-- Prove2me | Theorems.Thm_DerivativeChainContinuation_single_centered_mode_chain_bound
-- name    : DerivativeChainContinuation.single_centered_mode_chain_bound
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T21:14:09.070916+00:00
-- url     : https://prove2.me/theorems/4b004386-63ba-4d17-bd40-cda8a805e2a4
-- title:
--   One centered mode gives a complete chain with the radial variance bound
-- statement:
--   Let $p\in\mathbb C[X]$ be monic of degree $n$, with centroid $u$, and let $2\le q\le n$. Suppose every centered coefficient indexed by $2\le j\le n$ outside $j=q$ is zero. If all roots lie in $|z-a|\le D$, with $D\ge0$, an actual derivative chain starts at $u$ and satisfies
--
--   $$L(z)\le\sqrt{D^2-|u-a|^2}.$$
--
--   If the remaining coefficient of $X^{n-q}$ is zero, the same chain has cost zero. For a finite complex path $z_0,\ldots,z_{N-1}$, write $L(z)=\sum_{i=0}^{N-2}|z_{i+1}-z_i|$. An actual derivative chain for a degree-$N$ polynomial $p$ satisfies $p^{(N-i-1)}(z_i)=0$ for every $0\le i<N$.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/SingleModeChain.lean#L7-L38

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

theorem DerivativeChainContinuation.single_centered_mode_chain_bound (p : Polynomial ℂ) (hp : p.Monic) (n q : ℕ)
    (hn : p.natDegree=n) (hq : 2 ≤ q) (hqn : q ≤ n)
    (hsupport : ∀ j ≤ n, 2 ≤ j → j ≠ q → (centeredSource p).coeff (n-j)=0)
    (a : ℂ) (D : ℝ) (hD : 0 ≤ D) (hbound : ∀ z : ℂ, p.eval z=0 → ‖z-a‖ ≤ D) :
    ∃ z : Fin n → ℂ,
      (∀ i, (derivative^[n-(i.val+1)] p).eval (z i)=0) ∧
      z ⟨0,by omega⟩=rootCentroid p ∧ chainCost z ≤ Real.sqrt (D^2-‖rootCentroid p-a‖^2) ∧
      ((centeredSource p).coeff (n-q)=0 → chainCost z=0) := by sorry
