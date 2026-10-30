-- Prove2me | Theorems.Thm_DerivativeChainContinuation_collinear_transport_chain_family
-- name    : DerivativeChainContinuation.collinear_transport_chain_family
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T17:46:17.57902+00:00
-- url     : https://prove2.me/theorems/07a1f658-0df6-4df3-b2da-83a29d89c392
-- title:
--   Transport chains for collinear complex roots
-- statement:
--   Let $n>0$, let $a_0,\ldots,a_n\in\mathbb R$, and let $o,c\in\mathbb C$ with $c
--   e0$. Put $A_i=o+ca_i$ and $\mu=(n+1)^{-1}\sum_i A_i$. There is a complex derivative chain $z^{(j)}$ ending at each $A_j$ for which
--
--   $$\sum_j L(z^{(j)})^2\le\frac{28}3\sum_i|A_i-\mu|^2,\qquad L(z)=\sum_{i=0}^{n-1}|z_{i+1}-z_i|.$$
--
--   Affine transport transfers the real-root estimate to any complex line.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/CollinearTransport.lean#L35-L70

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CollinearTransport
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped BigOperators

theorem DerivativeChainContinuation.collinear_transport_chain_family (n : ℕ) (hn : 0<n)
    (a : Fin (n+1) → ℝ) (o c : ℂ) (hc : c≠0) :
    ∃ z : Fin (n+1) → Fin (n+1) → ℂ,
      (∀ j,IsChain (fun i => o+c*(a i : ℂ)) (z j)) ∧
      (∀ j,z j (Fin.last n)=o+c*(a j : ℂ)) ∧
      (∑ j,(chainCost (z j))^2) ≤ (28/3 : ℝ)*
        (∑ i,‖o+c*(a i : ℂ)-complexCentroid (fun j => o+c*(a j : ℂ))‖^2) := by sorry
