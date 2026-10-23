-- Prove2me | Theorems.Thm_DoubleAuctionEff_Repeated_auction_gain
-- name    : DoubleAuctionEff.Repeated.auction_gain
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:21:59.115642+00:00
-- url     : https://prove2.me/theorems/31502733-2865-4db8-a359-596ff699246f
-- title:
--   Proof of Theorem 16, p. 19 — Assumption 5 bounds the utility gain of an auction below by δ_i times the agent's surplus: u_i(x^t_i) ≥ u_i(x^{t−1}_i) + δ_i CS_i(x^{t−1})
-- statement:
--   Let $u$ satisfy Assumption 1, let $D$ be the indifference price at the endowment $x^0$, and let $p$ be a supergradient of $D$ at $\bar x$ with $D(\bar x)=c\in\mathbb R$; write $CS=c-p\cdot\bar x$ for the agent's surplus and $x^1=x^0+\bar x-(p\cdot\bar x)g$. Let $r>0$ and $\delta$ satisfy the inequality of Assumption 5 at radius $r$, i.e. $u(z+rg)\ge u(z)+\delta r$ for all $z\in\mathbb B(r)$. If
--   $$x^0+\bar x-cg\in\mathbb B(r)\quad\text{and}\quad CS\le r,$$
--   then
--   $$u(x^1)\ge u(x^0)+\delta\,CS.$$
--
--   Summed over the auctions $s=1,\dots,t$ and over agents, this gives the $1/t$ rate of Theorem 16.
--
--   **Formalization Note** The ball condition is placed on $x^0+\bar x-cg$, the point at which Assumption 5 is applied (since $x^1=x^0+\bar x-cg+CS\cdot g$). The paper instead asks $x^1\in\mathbb B(r)$, which does not guarantee that this point lies in $\mathbb B(r)$.
-- source:
--   T. Pennanen, Efficient allocations in double auction markets, arXiv:2001.02071v2, p. 19, proof of Theorem 16 (CS_i(x^{t−1}) := D_i(x̄^t_i) − p^t·x̄^t_i and the display after 'Assumption 5 gives')

import Mathlib
import Definitions.Def_DoubleAuctionEff_Repeated_Model

open Matrix

namespace DoubleAuctionEff.Repeated
theorem auction_gain {J : Type*} [Fintype J] (u : (J → ℝ) → EReal) (g x0 xbar p : J → ℝ) (h1 : Assumption1 u g) (hp : IsSupergrad (indiffPrice u g x0) xbar p) (c : ℝ) (hc : indiffPrice u g x0 xbar = (c : EReal)) (r δ : ℝ) (hr : 0 < r) (h5 : Assumption5At u g r δ) (hball : x0 + xbar - c • g ∈ Metric.closedBall (0 : J → ℝ) r) (hsurplus : c - p ⬝ᵥ xbar ≤ r) : u x0 + ((δ * (c - p ⬝ᵥ xbar) : ℝ) : EReal) ≤ u (x0 + xbar - (p ⬝ᵥ xbar) • g) := by sorry
end DoubleAuctionEff.Repeated
