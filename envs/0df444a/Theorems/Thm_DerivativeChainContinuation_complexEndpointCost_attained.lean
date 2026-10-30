-- Prove2me | Theorems.Thm_DerivativeChainContinuation_complexEndpointCost_attained
-- name    : DerivativeChainContinuation.complexEndpointCost_attained
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T17:52:41.982061+00:00
-- url     : https://prove2.me/theorems/9156f19d-40c2-4f5b-b97d-e14c47e4b2f3
-- title:
--   Attainment of the minimum complex endpoint-chain cost
-- statement:
--   Let $n\ge0$, let $a_0,\ldots,a_n\in\mathbb C$, and let $v\in\mathbb C$. Suppose at least one derivative chain for $p(X)=\prod_i(X-a_i)$ ends at $v$. Then such a chain $z$ attains the infimum $C_a(v)$ of chain lengths:
--
--   $$z_n=v,\qquad p^{(n-i)}(z_i)=0\ (0\le i\le n),\qquad\sum_{i=0}^{n-1}|z_{i+1}-z_i|=C_a(v).$$
--
--   This upgrades endpoint infima to actual minimizing chains.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/RealTransportComplete.lean#L31-L52

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CollinearTransport
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped BigOperators

theorem DerivativeChainContinuation.complexEndpointCost_attained {n : ℕ} (a : Fin (n+1) → ℂ) (v : ℂ)
    (hex : ∃ z : Fin (n+1) → ℂ,IsChain a z ∧ z (Fin.last n)=v) :
    ∃ z : Fin (n+1) → ℂ,IsChain a z ∧ z (Fin.last n)=v ∧
      chainCost z=complexEndpointCost a v := by sorry
