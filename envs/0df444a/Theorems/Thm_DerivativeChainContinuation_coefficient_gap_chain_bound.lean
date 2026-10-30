-- Prove2me | Theorems.Thm_DerivativeChainContinuation_coefficient_gap_chain_bound
-- name    : DerivativeChainContinuation.coefficient_gap_chain_bound
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T21:09:02.370995+00:00
-- url     : https://prove2.me/theorems/7e60482c-292a-4fa4-bcb7-1b8fc6aa1a3e
-- title:
--   A centered coefficient gap controls a complete derivative chain
-- statement:
--   Let $p\in\mathbb C[X]$ be monic of degree $n$, with root centroid $u$. Suppose $1\le h\le k\le n-2$ and
--
--   $$p(X+u)=X^n+AX^k+Q(X),\qquad \deg Q<h,$$
--
--   where $A\in\mathbb C$ and $Q\in\mathbb C[X]$. If all roots of $p$ lie in $|z|\le R$ for $R\ge0$, there is an actual derivative chain starting at $u$ with
--
--   $$L(z)\le\sqrt{h+1}\sqrt{R^2-|u|^2},\qquad A=0\Longrightarrow L(z)\le\sqrt h\sqrt{R^2-|u|^2}.$$
--
--   For a finite complex path $z_0,\ldots,z_{N-1}$, write $L(z)=\sum_{i=0}^{N-2}|z_{i+1}-z_i|$. An actual derivative chain for a degree-$N$ polynomial $p$ satisfies $p^{(N-i-1)}(z_i)=0$ for every $0\le i<N$. The conclusion concerns the full polynomial derivative tower.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/CoefficientGapChain.lean#L9-L60

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
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate




end DerivativeChainContinuation

theorem DerivativeChainContinuation.coefficient_gap_chain_bound (p : Polynomial ℂ) (hp : p.Monic) (n h k : ℕ)
    (hn : p.natDegree=n) (hh : 1 ≤ h) (hhk : h ≤ k) (hk : k ≤ n-2)
    (A : ℂ) (Q : Polynomial ℂ) (hQ : Q.natDegree < h)
    (hgap : centeredSource p=X^n+C A*X^k+Q)
    (R : ℝ) (hR : 0 ≤ R) (hbound : ∀ z : ℂ, p.eval z=0 → ‖z‖ ≤ R) :
    ∃ z : Fin n → ℂ,
      (∀ i, (derivative^[n-(i.val+1)] p).eval (z i)=0) ∧
      z ⟨0,by omega⟩=rootCentroid p ∧
      chainCost z ≤ Real.sqrt (h+1)*Real.sqrt (R^2-‖rootCentroid p‖^2) ∧
      (A=0 → chainCost z ≤ Real.sqrt h*Real.sqrt (R^2-‖rootCentroid p‖^2)) := by sorry
