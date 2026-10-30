-- Prove2me | Theorems.Thm_DerivativeChainContinuation_sparse_cluster_chain_bound
-- name    : DerivativeChainContinuation.sparse_cluster_chain_bound
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T21:02:09.591057+00:00
-- url     : https://prove2.me/theorems/c3e34ea8-7e8f-414c-b087-31a0765f618e
-- title:
--   A centered coefficient block yields a complete chain with optional return
-- statement:
--   Let $p\in\mathbb C[X]$ be monic of degree $n$, with centroid $u$. Let $1\le h$, $2\le q\le r-h$ and $r\le n$. Among centered modes $2\le j\le n$, assume the coefficient of $X^{n-j}$ vanishes outside $\{q\}\cup\{r-h+1,\ldots,r\}$. If all roots lie in $|z-a|\le D$, where $a\in\mathbb C$ and $D\ge0$, an actual derivative chain starts at $u$, stays at $u$ from index $r$, and satisfies
--
--   $$L(z)\le\left(\mathbf1_{r<n}+\sqrt{h+1}\right)\sqrt{D^2-|u-a|^2}.$$
--
--   When the centered coefficient of $X^{n-q}$ is zero, replace $\sqrt{h+1}$ by $\sqrt h$. If $r=n$, the asserted return interval is empty and its indicator cost is zero. For a finite complex path $z_0,\ldots,z_{N-1}$, write $L(z)=\sum_{i=0}^{N-2}|z_{i+1}-z_i|$. An actual derivative chain for a degree-$N$ polynomial $p$ satisfies $p^{(N-i-1)}(z_i)=0$ for every $0\le i<N$.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/SparseClusterChain.lean#L10-L70

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

theorem DerivativeChainContinuation.sparse_cluster_chain_bound (p : Polynomial ℂ) (hp : p.Monic)
    (n r h q : ℕ) (hn : p.natDegree=n) (hh : 1 ≤ h)
    (hq : 2 ≤ q) (hqr : q ≤ r-h) (hrn : r ≤ n)
    (hsupport : ∀ j ≤ n, 2 ≤ j → j ≠ q → (j ≤ r-h ∨ r < j) →
      (centeredSource p).coeff (n-j)=0)
    (a : ℂ) (D : ℝ) (hD : 0 ≤ D) (hbound : ∀ z : ℂ, p.eval z=0 → ‖z-a‖ ≤ D) :
    ∃ z : Fin n → ℂ,
      (∀ i, (derivative^[n-(i.val+1)] p).eval (z i)=0) ∧
      z ⟨0,by omega⟩=rootCentroid p ∧ (∀ i, r ≤ i.val → z i=rootCentroid p) ∧
      chainCost z ≤ ((if r=n then 0 else 1)+Real.sqrt (h+1 : ℕ))*Real.sqrt (D^2-‖rootCentroid p-a‖^2) ∧
      ((centeredSource p).coeff (n-q)=0 →
        chainCost z ≤ ((if r=n then 0 else 1)+Real.sqrt h)*Real.sqrt (D^2-‖rootCentroid p-a‖^2)) := by sorry
