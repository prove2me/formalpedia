-- Prove2me | Theorems.Thm_DerivativeChainContinuation_at_most_two_centered_modes_chain
-- name    : DerivativeChainContinuation.at_most_two_centered_modes_chain
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T21:04:15.327061+00:00
-- url     : https://prove2.me/theorems/f4d42c97-2eaa-437b-a427-a200f686f307
-- title:
--   At most two centered modes give a uniform complete-chain bound
-- statement:
--   Let $p\in\mathbb C[X]$ be monic of positive degree $n$, with centroid $u$. Suppose at most two of its centered coefficients indexed by $2\le j\le n$ are nonzero. If all roots lie in $|z-a|\le D$ for $a\in\mathbb C$ and $D\ge0$, an actual derivative chain starting at $u$ satisfies
--
--   $$L(z)\le(1+\sqrt2)\sqrt{D^2-|u-a|^2}.$$
--
--   The centered coefficient indexed by $j$ is the coefficient of $X^{n-j}$ in $p(X+u)$. For a finite complex path $z_0,\ldots,z_{N-1}$, write $L(z)=\sum_{i=0}^{N-2}|z_{i+1}-z_i|$. An actual derivative chain for a degree-$N$ polynomial $p$ satisfies $p^{(N-i-1)}(z_i)=0$ for every $0\le i<N$.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/AtMostTwoModes.lean#L8-L78

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
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate




end DerivativeChainContinuation

theorem DerivativeChainContinuation.at_most_two_centered_modes_chain (p : Polynomial ℂ) (hp : p.Monic)
    (n : ℕ) (hn : p.natDegree=n) (hnpos : 0 < n)
    (hmodes : (centeredModeSupport p).card ≤ 2)
    (a : ℂ) (D : ℝ) (hD : 0 ≤ D) (hbound : ∀ z : ℂ, p.eval z=0 → ‖z-a‖ ≤ D) :
    ∃ z : Fin n → ℂ,
      (∀ i, (derivative^[n-(i.val+1)] p).eval (z i)=0) ∧
      z ⟨0,hnpos⟩=rootCentroid p ∧
      chainCost z ≤ (1+Real.sqrt 2)*Real.sqrt (D^2-‖rootCentroid p-a‖^2) := by sorry
