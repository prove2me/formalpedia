-- Prove2me | Theorems.Thm_DerivativeChainContinuation_real_tower_centered
-- name    : DerivativeChainContinuation.real_tower_centered
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T16:53:56.432167+00:00
-- url     : https://prove2.me/theorems/9195a002-b6b5-49c1-9763-56932693af15
-- title:
--   Centering propagates down a real derivative tower
-- statement:
--   Let $r_k$ be real rows with $k+1$ entries, and suppose each row below level $n$ interlaces the next row and its root polynomial is the normalized derivative of the next root polynomial. If the top row is centered, then every lower row is centered:
--
--   $$\sum_i r_n(i)=0\quad\Longrightarrow\quad\sum_i r_k(i)=0\qquad(0\le k\le n).$$
--
--   This preserves the common centroid required by the square-moment profile.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/RealVarianceProfile.lean#L7-L25

import Mathlib
import Definitions.Def_DerivativeChainContinuation_RealTower
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped BigOperators

theorem DerivativeChainContinuation.real_tower_centered (r : RealRows) (n : ℕ)
    (hstep : ∀ k<n,RealRowStep r k) (hc : ∑ i,r n i = 0) :
    ∀ k≤n,∑ i,r k i = 0 := by sorry
