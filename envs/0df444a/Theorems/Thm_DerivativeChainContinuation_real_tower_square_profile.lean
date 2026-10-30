-- Prove2me | Theorems.Thm_DerivativeChainContinuation_real_tower_square_profile
-- name    : DerivativeChainContinuation.real_tower_square_profile
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T17:02:32.739608+00:00
-- url     : https://prove2.me/theorems/fc692406-1d36-4b6c-8696-f0436d500748
-- title:
--   Exact square-moment profile of a centered derivative tower
-- statement:
--   Let $r_k$ be an interlacing real derivative tower through level $n$, with centered top row. For every $0\le k\le n$,
--
--   $$n(n+1)\sum_i r_k(i)^2=k(k+1)\sum_i r_n(i)^2.$$
--
--   The identity expresses every row variance using the variance of the source polynomial.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/RealVarianceProfile.lean#L27-L60

import Mathlib
import Definitions.Def_DerivativeChainContinuation_RealTower
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped BigOperators

theorem DerivativeChainContinuation.real_tower_square_profile (r : RealRows) (n : ℕ)
    (hstep : ∀ k<n,RealRowStep r k) (hc : ∑ i,r n i = 0) :
    ∀ k≤n,(n : ℝ)*(n+1)*(∑ i,(r k i)^2) =
      (k : ℝ)*(k+1)*(∑ i,(r n i)^2) := by sorry
