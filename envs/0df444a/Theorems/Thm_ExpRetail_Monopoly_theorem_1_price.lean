-- Prove2me | Theorems.Thm_ExpRetail_Monopoly_theorem_1_price
-- name    : ExpRetail.Monopoly.theorem_1_price
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:12:24.164297+00:00
-- url     : https://prove2.me/theorems/b6ffd2c0-d3f4-4638-933c-24f8be358ecf
-- title:
--   Theorem 1 (p∗ > p∗N), p. 12 — every optimal price with a free experience exceeds every no-experience optimal price
-- statement:
--   Consider the monopoly model of §3.1 under the standing assumptions $t>0$, $\eta>0$, $s>0$, $\lambda>0$, with $u^m$ and $c^m$ arbitrary. Let $\pi$ be the profit (4) with a free experience of quality $u^x$, and $\pi^N$ the profit (5) without one.
--
--   1. A no-experience optimal price $p^{*N}$ exists, and at every such price the optimal profit $\pi^{*N}=\sup_p\pi^N(p)$ is attained: $\pi^{*N}=\pi^N(p^{*N})$.
--   2. For every quality $u^x\ge 0$, an optimal price $p^*$ exists, and at every such price $\pi^*(u^x)=\sup_p\pi(p)=\pi(p^*)$.
--   3. For every $u^x\ge0$, every optimal price with the experience exceeds every no-experience optimal price:
--   $$p^*>p^{*N}\qquad\forall\,u^x\ge 0 .$$
--
--   Offering a free experience, of any quality, raises the price of the main product. Parts 1 and 2 make precise the paper's notation $p^*$, $p^{*N}$, $\pi^*$, $\pi^{*N}$ for optimal solutions, which presupposes that they exist.
--
--   **Formalization Note** Prices range over all of $\mathbb R$. Existence of optimal prices is asserted as a conclusion, never assumed; uniqueness is not claimed, so the inequality is stated for every pair of optimal prices.
-- source:
--   Mutlu, El-Amine & Sahin, Offering memories to sell goods?, SSRN working paper 4617261 (PDF of 2023-10-30), p. 12, Theorem 1 ("p∗ > p∗N, ∀u^x ≥ 0"); notation p. 11

import Mathlib
import Definitions.Def_ExpRetail_Monopoly_Model

namespace ExpRetail.Monopoly

theorem theorem_1_price (P : Params) (hP : P.Standing) :
    (∃ pN : ℝ, IsOptPriceN P pN) ∧
    (∀ pN : ℝ, IsOptPriceN P pN → optProfitN P = profitN P pN) ∧
    ∀ ux : ℝ, 0 ≤ ux →
      (∃ p : ℝ, IsOptPrice P ux p) ∧
      (∀ p : ℝ, IsOptPrice P ux p → optProfit P ux = profit P ux p) ∧
      ∀ p pN : ℝ, IsOptPrice P ux p → IsOptPriceN P pN → pN < p := by sorry

end ExpRetail.Monopoly
