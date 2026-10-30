-- Prove2me | Theorems.Thm_DerivativeChainContinuation_centered_ordered_transport
-- name    : DerivativeChainContinuation.centered_ordered_transport
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T17:41:38.787295+00:00
-- url     : https://prove2.me/theorems/1f2eb1c6-2f7c-406a-9ad0-0afd17d4f0f5
-- title:
--   Transport chains for a centered ordered real source
-- statement:
--   Let $n>0$ and let $a_0\le\cdots\le a_n$ be real numbers with $\sum_i a_i=0$. For every endpoint $a_j$ there exists a real chain $z^{(j)}_0,\ldots,z^{(j)}_n$, with $z^{(j)}_i$ a root of $p_a^{(n-i)}$ and $z^{(j)}_n=a_j$, such that
--
--   $$\sum_j\left(\sum_{i=0}^{n-1}|z^{(j)}_{i+1}-z^{(j)}_i|\right)^2\le\frac{28}3\sum_i a_i^2.$$
--
--   This is the centered, ordered form of the real transport theorem.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/RealTransportBound.lean#L57-L73

import Mathlib
import Definitions.Def_DerivativeChainContinuation_RealHistories
import Definitions.Def_DerivativeChainContinuation_RealInterlacing
import Definitions.Def_DerivativeChainContinuation_RealTransportBound
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped BigOperators

theorem DerivativeChainContinuation.centered_ordered_transport (n : ℕ) (hn : 0<n) (a : Fin (n+1) → ℝ)
    (ha : Monotone a) (hc : ∑ i,a i=0) :
    ∃ z : Fin (n+1) → Fin (n+1) → ℝ,
      (∀ j,IsRealDerivativeChain (realRootProduct a) n (z j)) ∧
      (∀ j,z j (Fin.last n)=a j) ∧
      (∑ j,(realChainCost (z j))^2) ≤ (28/3 : ℝ)*(∑ i,(a i)^2) := by sorry
