-- Prove2me | Theorems.Thm_DerivativeChainContinuation_finite_derivative_chains
-- name    : DerivativeChainContinuation.finite_derivative_chains
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T17:50:39.160683+00:00
-- url     : https://prove2.me/theorems/713b4df5-32bc-4f3d-97c0-82a7fd1d3f96
-- title:
--   Finiteness of the derivative-chain set
-- statement:
--   Let $n\ge0$ and $a_0,\ldots,a_n\in\mathbb C$. For $p(X)=\prod_i(X-a_i)$, the set of sequences choosing a root of $p^{(n-i)}$ at every level is finite:
--
--   $$\#\{z\in\mathbb C^{n+1}:p^{(n-i)}(z_i)=0\text{ for every }0\le i\le n\}<\infty.$$
--
--   This ensures that a nonempty endpoint-constrained chain family has a length minimizer.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/RealTransportComplete.lean#L9-L29

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped BigOperators

theorem DerivativeChainContinuation.finite_derivative_chains {n : ℕ} (a : Fin (n+1) → ℂ) :
    {z : Fin (n+1) → ℂ | IsChain a z}.Finite := by sorry
