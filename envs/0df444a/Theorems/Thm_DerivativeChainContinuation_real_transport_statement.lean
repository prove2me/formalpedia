-- Prove2me | Theorems.Thm_DerivativeChainContinuation_real_transport_statement
-- name    : DerivativeChainContinuation.real_transport_statement
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T17:57:13.149991+00:00
-- url     : https://prove2.me/theorems/1cd3870f-f7df-4eea-882c-1fcbc6e63b91
-- title:
--   Explicit squared endpoint transport bound for collinear roots
-- statement:
--   Let $n\ge0$, let $a_0,\ldots,a_n\in\mathbb C$, and suppose $a_i=o+cr_i$ for some $o,c\in\mathbb C$ with $c
--   e0$ and $r_i\in\mathbb R$. Set $p(X)=\prod_i(X-a_i)$, $\mu=(n+1)^{-1}\sum_i a_i$, and assume $V=\sum_i|a_i-\mu|^2>0$. Define $C_a(v)$ as the infimum of $\sum_{i=0}^{n-1}|z_{i+1}-z_i|$ over sequences with $p^{(n-i)}(z_i)=0$ and $z_n=v$. Then
--
--   $$\frac{\sum_{j=0}^{n}C_a(a_j)^2}{\sum_{j=0}^{n}|a_j-\mu|^2}\le\frac{28}3.$$
--
--   The bound is uniform in degree and includes repeated roots. The endpoint cost is expanded directly in terms of the source polynomial and its derivatives in the formal statement.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/RealTransportStatement.lean#L22-L28

import Mathlib
import Definitions.Def_DerivativeChainContinuation_RealTransportStatement
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped BigOperators

theorem DerivativeChainContinuation.real_transport_statement {n : ℕ} (a : Fin (n+1) → ℂ)
    (hline : ∃ o c : ℂ,c≠0 ∧ ∃ r : Fin (n+1) → ℝ,∀ i,a i=o+c*(r i : ℂ))
    (hvariance : 0 < ∑ i,‖a i-(∑ j,a j)/(n+1 : ℂ)‖^2) :
    (∑ i,(explicitEndpointCost a (a i))^2)/
      (∑ i,‖a i-(∑ j,a j)/(n+1 : ℂ)‖^2) ≤ (28/3 : ℝ) := by sorry
