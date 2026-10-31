-- Prove2me | Theorems.Thm_DoubleAuctionEff_Repeated_remark_6
-- name    : DoubleAuctionEff.Repeated.remark_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:22:01.003566+00:00
-- url     : https://prove2.me/theorems/8522b6c3-e573-41b8-81de-2d7d3ad3b94f
-- title:
--   Remark 6, p. 12 — a market clearing trade is a Pareto improvement: D_i(x̄_i) − p·x̄_i ≥ 0 and u_i(x^1_i) ≥ u_i(x^0_i), strictly unless D_i(x̄_i) = p·x̄_i
-- statement:
--   Let $u$ satisfy Assumption 1, let $D$ be the indifference price at the endowment $x^0$, and let $p$ be a supergradient of $D$ at $\bar x$, with $D(\bar x)=c\in\mathbb R$. Put $x^1=x^0+\bar x-(p\cdot\bar x)g$. Then
--
--   1. $c-p\cdot\bar x\ge0$;
--   2. $u(x^1)\ge u(x^0+\bar x-cg)$;
--   3. $u(x^0+\bar x-cg)\ge u(x^0)$;
--   4. $u(x^1)\ge u(x^0)$; and
--   5. if $c\ne p\cdot\bar x$, then
--   $$u(x^1)>u(x^0).$$
--
--   So no agent is worse off after market clearing, and an agent with positive consumer surplus is strictly better off.
--
--   **Formalization Note** No domain hypothesis is needed: the finiteness of $D(\bar x)$ built into the supergradient forces $x^0\in\operatorname{dom}u$.
-- source:
--   T. Pennanen, Efficient allocations in double auction markets, arXiv:2001.02071v2, p. 12, Remark 6

import Mathlib
import Definitions.Def_DoubleAuctionEff_Repeated_Model

open Matrix

namespace DoubleAuctionEff.Repeated
theorem remark_6 {J : Type*} [Fintype J] (u : (J → ℝ) → EReal) (g x0 xbar p : J → ℝ) (h1 : Assumption1 u g) (hp : IsSupergrad (indiffPrice u g x0) xbar p) (c : ℝ) (hc : indiffPrice u g x0 xbar = (c : EReal)) : 0 ≤ c - p ⬝ᵥ xbar ∧ u (x0 + xbar - c • g) ≤ u (x0 + xbar - (p ⬝ᵥ xbar) • g) ∧ u x0 ≤ u (x0 + xbar - c • g) ∧ u x0 ≤ u (x0 + xbar - (p ⬝ᵥ xbar) • g) ∧ (c ≠ p ⬝ᵥ xbar → u x0 < u (x0 + xbar - (p ⬝ᵥ xbar) • g)) := by sorry
end DoubleAuctionEff.Repeated
