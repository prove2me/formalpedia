-- Prove2me | Theorems.Thm_DerivativeChainContinuation_real_derivative_interlacing
-- name    : DerivativeChainContinuation.real_derivative_interlacing
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T17:35:20.108893+00:00
-- url     : https://prove2.me/theorems/af002a13-d293-4f49-a05f-320b10b9a1fa
-- title:
--   Derivative interlacing allowing repeated real roots
-- statement:
--   Let $n\ge0$ and $a_0\le\cdots\le a_{n+1}$ be real numbers, allowing repetitions. There exist $b_0\le\cdots\le b_n$ with $a_i\le b_i\le a_{i+1}$ such that
--
--   $$\left(\prod_{i=0}^{n+1}(X-a_i)\right)^{\prime}=(n+2)\prod_{i=0}^{n}(X-b_i).$$
--
--   This extends the tower construction to arbitrary real-root multiplicities.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/RepeatedInterlacing.lean#L17-L80

import Mathlib
import Definitions.Def_DerivativeChainContinuation_RealInterlacing
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped BigOperators
open Filter Topology

theorem DerivativeChainContinuation.real_derivative_interlacing (n : ℕ) (a : Fin (n+2) → ℝ)
    (ha : Monotone a) :
    ∃ b : Fin (n+1) → ℝ, Monotone b ∧
      (∀ i, a i.castSucc ≤ b i ∧ b i ≤ a i.succ) ∧
      (realRootProduct a).derivative = C (n+2 : ℝ) * realRootProduct b := by sorry
