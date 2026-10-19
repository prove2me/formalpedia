-- Prove2me | Theorems.Thm_DERAggregation_Unregulated_lemma_4
-- name    : DERAggregation.Unregulated.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T11:25:06.203083+00:00
-- url     : https://prove2.me/theorems/2176528c-a76b-4490-882b-91e9a25c64e5
-- title:
--   Lemma 4, p. 11 — the aggregator's optimal two-part offer passes the wholesale price through and charges the selling surplus
-- statement:
--   Consider one prosumer with utility $u$, capacity $C$ and bound $Z$ satisfying Assumption 1, at wholesale price $\lambda$, and let $z_1\in(0,Z)$ satisfy $u'(z_1)=\lambda$ as in (12). Write $\Pi(P,p)=P\,\mathbf 1\{x^*>0\}+(\lambda-p)x^*$ for the aggregator's profit (13) at an optimal response $(x^*,d^*)$ of the prosumer to the offer $(P,p)$.
--
--   1. If $z_1<C$, the offer
--   $$p^*=\lambda,\qquad P^*=\lambda(C-z_1)+u(z_1)-u(C) \tag{16}$$
--   has $P^*\ge0$, the response "sell $C-z_1$, buy nothing" is optimal for the prosumer, and the resulting profit $P^*$ is at least the profit of every offer $(P,p)\in\mathbb R^2_+$ against every optimal response to it.
--   2. If $z_1\ge C$, then for every offer with $P\ge0$ and $0\le p\le\lambda$ and every optimal response, $\Pi(P,p)=0$: the prosumer does not sell DER supply to the aggregator profitably.
--
--   The aggregator passes the locational price through as the unit price and extracts the prosumer's whole surplus from selling as the participation fee.
--
--   **Formalization Note** Part 1 holds against all nonnegative offers, including $p>\lambda$. Part 2 is stated under the standing restriction $p\le\lambda$ of p. 10 (for $p>\lambda$ the aggregator's profit can be negative); its conclusion is $\Pi=0$, as printed, rather than $x^*=0$, since at $P=0$, $p=\lambda$ selling and buying back can tie.
-- source:
--   Gao, Alshehri, Birge, Aggregating Distributed Energy Resources: Efficiency and Market Power, working paper, SSRN abstract 3931052 (PDF of September 26, 2021), p. 11, Lemma 4, (13)–(16); proof pp. 42–43

import Mathlib
import Definitions.Def_DERAggregation_Unregulated_Setting

namespace DERAggregation.Unregulated

open Set

/-- Lemma 4 (p. 11). Under Assumption 1, with `z₁ ∈ (0, Z)`, `u'(z₁) = λ`: if `z₁ < C`, the offer
`p* = λ`, `P* = λ(C − z₁) + u(z₁) − u(C)` (16) is nonnegative, `(C − z₁, 0)` is an optimal response
to it, and it earns at least as much as every offer `(P, p) ∈ ℝ²₊` against every optimal response;
if `z₁ ≥ C`, every offer with `P ≥ 0`, `0 ≤ p ≤ λ` earns `Π = 0` against every optimal response. -/
theorem lemma_4 (u : ℝ → ℝ) (C Z : ℝ) (hu : UtilAssm u C Z) (lam z1 : ℝ)
    (hz1 : z1 ∈ Ioo 0 Z) (hz1d : deriv u z1 = lam) :
    (z1 < C →
      0 ≤ lam * (C - z1) + u z1 - u C ∧
      IsResp u C Z lam (lam * (C - z1) + u z1 - u C) lam (C - z1) 0 ∧
      ∀ P p x d : ℝ, 0 ≤ P → 0 ≤ p → IsResp u C Z lam P p x d →
        aggProfit lam P p x ≤ aggProfit lam (lam * (C - z1) + u z1 - u C) lam (C - z1)) ∧
    (C ≤ z1 →
      ∀ P p x d : ℝ, 0 ≤ P → 0 ≤ p → p ≤ lam → IsResp u C Z lam P p x d →
        aggProfit lam P p x = 0) := by sorry

end DERAggregation.Unregulated
