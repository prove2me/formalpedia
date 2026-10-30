-- Prove2me | Theorems.Thm_DerivativeChainContinuation_full_real_transport_theorem
-- name    : DerivativeChainContinuation.full_real_transport_theorem
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T17:54:43.501304+00:00
-- url     : https://prove2.me/theorems/9c72740c-f5c9-48cc-942f-1c6161b3fdd3
-- title:
--   Complete real-line transport theorem with attained endpoint costs
-- statement:
--   Let $n\ge0$ and let $a_0,\ldots,a_n\in\mathbb C$ lie on a common complex affine line. Put $p(X)=\prod_i(X-a_i)$ and $\mu=(n+1)^{-1}\sum_i a_i$, and suppose $V=\sum_i|a_i-\mu|^2>0$. Let $C_a(v)$ be the infimum of lengths of sequences $z_0,\ldots,z_n$ with $p^{(n-i)}(z_i)=0$ and $z_n=v$. Every source endpoint $a_j$ has a chain attaining $C_a(a_j)$, and
--
--   $$\frac{\sum_{j=0}^{n}C_a(a_j)^2}{V}\le\frac{28}3.$$
--
--   This combines existence of minimizing chains with a degree-independent upper bound on their aggregate squared lengths. Repeated roots and arbitrary endpoint order are allowed.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/RealTransportComplete.lean#L57-L75

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CollinearTransport
import Definitions.Def_DerivativeChainContinuation_RealTransportComplete
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped BigOperators

theorem DerivativeChainContinuation.full_real_transport_theorem {n : ℕ} (a : Fin (n+1) → ℂ)
    (hline : OnComplexLine a)
    (hvariance : 0 < ∑ i,‖a i-complexCentroid a‖^2) :
    (∀ j,∃ z : Fin (n+1) → ℂ,IsChain a z ∧ z (Fin.last n)=a j ∧
      chainCost z=complexEndpointCost a (a j)) ∧
    uniformComplexTransportRatio a ≤ (28/3 : ℝ) := by sorry
