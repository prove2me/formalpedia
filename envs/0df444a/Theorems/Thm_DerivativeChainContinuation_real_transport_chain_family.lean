-- Prove2me | Theorems.Thm_DerivativeChainContinuation_real_transport_chain_family
-- name    : DerivativeChainContinuation.real_transport_chain_family
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T17:43:33.344885+00:00
-- url     : https://prove2.me/theorems/880e2694-d5be-4d0d-873e-1d0c89fa2f7d
-- title:
--   Transport chains for an arbitrary real source
-- statement:
--   Let $n>0$ and let $a_0,\ldots,a_n\in\mathbb R$, allowing repetitions and arbitrary order. Set $p_a(X)=\prod_i(X-a_i)$ and $\mu=(n+1)^{-1}\sum_i a_i$. There is a real derivative chain $z^{(j)}$ ending at every $a_j$ such that
--
--   $$\sum_j L(z^{(j)})^2\le\frac{28}3\sum_i(a_i-\mu)^2,\qquad L(z)=\sum_{i=0}^{n-1}|z_{i+1}-z_i|.$$
--
--   This removes centering and ordering assumptions from the chain construction.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/RealTransportGeneral.lean#L35-L71

import Mathlib
import Definitions.Def_DerivativeChainContinuation_RealHistories
import Definitions.Def_DerivativeChainContinuation_RealInterlacing
import Definitions.Def_DerivativeChainContinuation_RealTransportBound
import Definitions.Def_DerivativeChainContinuation_RealTransportGeneral
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped BigOperators

theorem DerivativeChainContinuation.real_transport_chain_family (n : ℕ) (hn : 0<n) (a : Fin (n+1) → ℝ) :
    ∃ z : Fin (n+1) → Fin (n+1) → ℝ,
      (∀ j,IsRealDerivativeChain (realRootProduct a) n (z j)) ∧
      (∀ j,z j (Fin.last n)=a j) ∧
      (∑ j,(realChainCost (z j))^2) ≤
        (28/3 : ℝ)*(∑ i,(a i-realCentroid a)^2) := by sorry
