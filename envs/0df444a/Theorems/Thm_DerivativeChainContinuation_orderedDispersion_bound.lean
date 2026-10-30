-- Prove2me | Theorems.Thm_DerivativeChainContinuation_orderedDispersion_bound
-- name    : DerivativeChainContinuation.orderedDispersion_bound
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T17:06:51.789393+00:00
-- url     : https://prove2.me/theorems/3d4178b5-5e40-4c1e-b73e-65141ed43e99
-- title:
--   Ordered dispersion from a square-moment bound
-- statement:
--   Let $m\ge0$, let $a_0,\ldots,a_m\in\mathbb R$, and let $K\ge0$ satisfy $\sum_i a_i^2=3m(m+1)K^2$. With $D(a)=\sum_{i=0}^{m}(2i-m)a_i$,
--
--   $$D(a)\le m(m+1)\sqrt{m+2}\,K.$$
--
--   This converts the tower square-moment profile into a transport potential bound.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/RankDispersion.lean#L41-L56

import Mathlib
import Definitions.Def_DerivativeChainContinuation_FiniteTransport
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped BigOperators

theorem DerivativeChainContinuation.orderedDispersion_bound (m : ℕ) (a : Fin (m+1) → ℝ)
    (K : ℝ) (hK : 0 ≤ K)
    (hs : ∑ i,(a i)^2 = 3*(m : ℝ)*(m+1)*K^2) :
    orderedDispersion a ≤ (m : ℝ)*(m+1)*Real.sqrt (m+2)*K := by sorry
