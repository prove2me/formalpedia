-- Prove2me | Theorems.Thm_DerivativeChainContinuation_realHistoryCost_attained
-- name    : DerivativeChainContinuation.realHistoryCost_attained
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T16:48:32.933988+00:00
-- url     : https://prove2.me/theorems/26264bc4-a5d4-4360-9165-72c68d665671
-- title:
--   Finite real row histories attain their endpoint cost
-- statement:
--   Let $r_k$ be a triangular family of real rows, with $k+1$ entries in row $k$. For every $n\ge0$ and every entry $v$ of row $n$, there is a history $z_0,\ldots,z_n$ selecting one entry of each row, ending at $z_n=v$, whose length attains the recursively defined minimum $H_r(n,v)$:
--
--   $$\sum_{i=0}^{n-1}|z_{i+1}-z_i|=H_r(n,v).$$
--
--   This supplies actual minimizing histories for the subsequent derivative-chain construction.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/RealHistories.lean#L22-L50

import Mathlib
import Definitions.Def_DerivativeChainContinuation_RealEndpointCost
import Definitions.Def_DerivativeChainContinuation_RealHistories
import Definitions.Def_DerivativeChainContinuation_RealTower
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped BigOperators

theorem DerivativeChainContinuation.realHistoryCost_attained (r : RealRows) (n : ℕ) (v : ℝ)
    (hv : ∃ j : Fin (n+1), v=r n j) :
    ∃ z : Fin (n+1) → ℝ, IsRowHistory r z ∧ z (Fin.last n)=v ∧
      realChainCost z=realHistoryCost r n v := by sorry
