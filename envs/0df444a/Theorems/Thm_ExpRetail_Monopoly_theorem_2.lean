-- Prove2me | Theorems.Thm_ExpRetail_Monopoly_theorem_2
-- name    : ExpRetail.Monopoly.theorem_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T05:12:38.400542+00:00
-- url     : https://prove2.me/theorems/8acc5f29-3145-4817-afd8-fcbb67d4b118
-- title:
--   Theorem 2, p. 13 — a free experience of quality u^x ≤ û^x raises both optimal profit and consumer welfare
-- statement:
--   Consider the monopoly model of §3.1 under the standing assumptions $t>0$, $\eta>0$, $s>0$, $\lambda>0$, with $u^m$ and $c^m$ arbitrary. Let $\pi$, $CS$ be the profit (4) and the log-sum consumer welfare with a free experience of quality $u^x$, and $\pi^N$, $CS^N$ the profit (5) and the consumer welfare without one. Then:
--
--   1. **Low quality is win-win.** A no-experience optimal price $p^{*N}$ exists, and there is a threshold $\hat u^x>0$ such that for every quality $0\le u^x\le\hat u^x$ an optimal price $p^*$ exists and, for every such $p^*$ and every $p^{*N}$,
--   $$\pi(p^*)>\pi^N(p^{*N})\qquad\text{and}\qquad CS(p^*)>CS^N(p^{*N}).$$
--   2. **Otherwise the retailer can be worse off.** There is a quality $u^x\ge0$ at which an optimal price $p^*$ exists and, for every such $p^*$ and every $p^{*N}$,
--   $$\pi(p^*)<\pi^N(p^{*N}).$$
--
--   This is the paper's Theorem 2: "there exists a threshold $\hat u^x>0$ such that offering an experience with utility $u^x\le\hat u^x$ improves both the retailer's profit and consumer welfare. Otherwise, an experiential offering can make the retailer and/or consumers worse off."
--
--   **Formalization Note** "Improves" is read as a strict improvement over the no-experience optimum, with welfare evaluated at the optimal prices. Existence of optimal prices is asserted, not assumed; uniqueness is not claimed. Consumer welfare is the logit log-sum (the paper does not define it; this convention reproduces Figure 1(d)). The informal second sentence is formalized as its retailer half: for every admissible parameter set some quality hurts the retailer at every optimal price. The theorem does not claim that every $u^x>\hat u^x$ hurts someone, and neither does the paper.
-- source:
--   Mutlu, El-Amine & Sahin, Offering memories to sell goods?, SSRN working paper 4617261 (PDF of 2023-10-30), p. 13, Theorem 2

import Mathlib
import Definitions.Def_ExpRetail_Monopoly_Model

namespace ExpRetail.Monopoly

theorem theorem_2 (P : Params) (hP : P.Standing) :
    ((∃ pN : ℝ, IsOptPriceN P pN) ∧
      ∃ uhat : ℝ, 0 < uhat ∧ ∀ ux : ℝ, 0 ≤ ux → ux ≤ uhat →
        (∃ p : ℝ, IsOptPrice P ux p) ∧
        ∀ p pN : ℝ, IsOptPrice P ux p → IsOptPriceN P pN →
          profitN P pN < profit P ux p ∧ CSN P pN < CS P ux p) ∧
    (∃ ux : ℝ, 0 ≤ ux ∧ (∃ p : ℝ, IsOptPrice P ux p) ∧
      ∀ p pN : ℝ, IsOptPrice P ux p → IsOptPriceN P pN →
        profit P ux p < profitN P pN) := by sorry

end ExpRetail.Monopoly
