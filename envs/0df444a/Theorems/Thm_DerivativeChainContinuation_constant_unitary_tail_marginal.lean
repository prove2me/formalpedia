-- Prove2me | Theorems.Thm_DerivativeChainContinuation_constant_unitary_tail_marginal
-- name    : DerivativeChainContinuation.constant_unitary_tail_marginal
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T19:44:47.302595+00:00
-- url     : https://prove2.me/theorems/35f1a492-c37a-413d-ba51-41f48390ace5
-- title:
--   A constant first unitary column gives uniform tail marginals
-- statement:
--   Let $Q$ be unitary in dimension $n+1$, where $n>0$, and suppose $Q_{i0}=1/\sqrt{n+1}$ for every row. Then $$\frac1n\sum_{j=1}^{n}|Q_{ij}|^2=\frac1{n+1}.$$ This supplies the exact uniform parent marginal for the differentiator kernel.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/UnitaryRootWeights.lean#L37-L54

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem DerivativeChainContinuation.constant_unitary_tail_marginal (n : ℕ) (hn : 0 < n)
    (Q : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hQ : Q ∈ unitaryGroup (Fin (n+1)) ℂ)
    (hfirst : ∀ i, Q i 0=((Real.sqrt (n+1:ℝ))⁻¹:ℂ)) (i : Fin (n+1)) :
    (∑ j : Fin n, (n:ℝ)⁻¹*Complex.normSq (Q i j.succ))=(n+1:ℝ)⁻¹ := by sorry
