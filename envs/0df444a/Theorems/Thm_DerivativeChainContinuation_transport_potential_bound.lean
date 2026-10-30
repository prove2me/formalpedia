-- Prove2me | Theorems.Thm_DerivativeChainContinuation_transport_potential_bound
-- name    : DerivativeChainContinuation.transport_potential_bound
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T17:21:51.352394+00:00
-- url     : https://prove2.me/theorems/ec38eeec-54d4-4411-990d-60ff42d735fd
-- title:
--   Telescoping potential bound for real row-history costs
-- statement:
--   Let $r_k$ be an interlacing real derivative tower through level $n+1$. Let $K\ge0$ satisfy $D(r_k)\le k(k+1)\sqrt{k+2}\,K$ for every $k\le n+1$, where $D$ denotes ordered dispersion. Writing $\overline H_r(k)$ for mean row-history cost,
--
--   $$\overline H_r(n+1)\le\frac{D(r_{n+1})}{(n+1)(n+2)}+4K(\sqrt{n+2}-\sqrt2).$$
--
--   This sums the one-step transport inequalities into a bound depending only on the top-row potential.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/TransportBudget.lean#L16-L64

import Mathlib
import Definitions.Def_DerivativeChainContinuation_FiniteTransport
import Definitions.Def_DerivativeChainContinuation_RealEndpointCost
import Definitions.Def_DerivativeChainContinuation_RealTower
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped BigOperators

theorem DerivativeChainContinuation.transport_potential_bound (r : RealRows) (n : ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hstep : ∀ k<n+1,RealRowStep r k)
    (hD : ∀ k≤n+1,orderedDispersion (r k) ≤ (k : ℝ)*(k+1)*Real.sqrt (k+2)*K) :
    meanHistoryCost r (n+1) ≤
      orderedDispersion (r (n+1))/((n+1 : ℝ)*(n+2))+
        4*K*(Real.sqrt (n+2)-Real.sqrt 2) := by sorry
