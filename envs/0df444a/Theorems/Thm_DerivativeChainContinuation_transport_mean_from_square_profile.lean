-- Prove2me | Theorems.Thm_DerivativeChainContinuation_transport_mean_from_square_profile
-- name    : DerivativeChainContinuation.transport_mean_from_square_profile
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T17:24:38.227118+00:00
-- url     : https://prove2.me/theorems/0c8ba2ff-4c76-494c-bd81-25b9ef3879ad
-- title:
--   Mean history cost from the exact square profile
-- statement:
--   Let $n>0$, $K\ge0$, and let $r_k$ be an interlacing real derivative tower through level $n$. Assume $\sum_i r_k(i)^2=3k(k+1)K^2$ for every $k\le n$. Then the average minimum history cost at the top row satisfies
--
--   $$\overline H_r(n)\le5\sqrt n\,K.$$
--
--   This is the normalized mean-cost estimate before substituting the source variance.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/TransportMean.lean#L22-L38

import Mathlib
import Definitions.Def_DerivativeChainContinuation_RealEndpointCost
import Definitions.Def_DerivativeChainContinuation_RealTower
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped BigOperators

theorem DerivativeChainContinuation.transport_mean_from_square_profile (r : RealRows) (n : ℕ) (hn : 0<n)
    (K : ℝ) (hK : 0 ≤ K) (hstep : ∀ k<n,RealRowStep r k)
    (hsquare : ∀ k≤n, ∑ i,(r k i)^2=3*(k : ℝ)*(k+1)*K^2) :
    meanHistoryCost r n ≤ 5*Real.sqrt n*K := by sorry
