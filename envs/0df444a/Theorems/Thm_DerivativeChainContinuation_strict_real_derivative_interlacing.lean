-- Prove2me | Theorems.Thm_DerivativeChainContinuation_strict_real_derivative_interlacing
-- name    : DerivativeChainContinuation.strict_real_derivative_interlacing
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T17:33:37.815087+00:00
-- url     : https://prove2.me/theorems/de0ad492-8830-4c2d-8e55-e90d627162ab
-- title:
--   Strict interlacing and factorization of a real derivative
-- statement:
--   Let $n\ge0$ and $a_0<\cdots<a_{n+1}$ be real numbers. There exist $b_0<\cdots<b_n$ with $a_i<b_i<a_{i+1}$ such that
--
--   $$\left(\prod_{i=0}^{n+1}(X-a_i)\right)^{\prime}=(n+2)\prod_{i=0}^{n}(X-b_i).$$
--
--   This supplies the strict-root case of the real derivative tower construction.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/RealInterlacing.lean#L24-L68

import Mathlib
import Definitions.Def_DerivativeChainContinuation_RealInterlacing
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped BigOperators

theorem DerivativeChainContinuation.strict_real_derivative_interlacing (n : ℕ) (a : Fin (n+2) → ℝ)
    (ha : StrictMono a) :
    ∃ b : Fin (n+1) → ℝ, StrictMono b ∧
      (∀ i, a i.castSucc < b i ∧ b i < a i.succ) ∧
      (realRootProduct a).derivative = C (n+2 : ℝ) * realRootProduct b := by sorry
