-- Prove2me | Theorems.Thm_DoubleAuctionEff_Repeated_Supplement_theorem_10
-- name    : DoubleAuctionEff.Repeated.Supplement.theorem_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T08:35:36.453865+00:00
-- url     : https://prove2.me/theorems/81bd6601-f2a0-4e2c-bd66-7ee14fbfcb59
-- title:
--   Theorem 10 — existence of an optimal market-clearing trade under Assumptions 1 and 3
-- statement:
--   Let $I$ be a finite set of agents and $J$ a finite set of assets. For each agent $i$, let $u_i:\mathbb R^J\to[-\infty,+\infty]$ be a utility function, let $x_i^0\in\mathbb R^J$ be the initial endowment, and let $g\in\mathbb R^J$ be the numeraire portfolio. Write $\operatorname{dom}u_i=\{z:u_i(z)>-\infty\}$. Assume each $u_i$ is upper semicontinuous, concave, and satisfies $u_i(z+rg)>u_i(z)$ whenever $z\in\operatorname{dom}u_i$ and $r>0$ (Assumption 1). Assume also that the only family $(d_i)_{i\in I}$ satisfying $\sum_i d_i=0$ and $u_i^\infty(d_i)\ge0$ for every $i$ is the zero family (Assumption 3). Here a nonnegative recession direction $d_i$ means that $u_i(z+\alpha d_i)\ge u_i(z)$ for every $z\in\operatorname{dom}u_i$ and every $\alpha>0$.
--
--   Define the indifference price by
--   $$
--   D_i(y_i)=\sup\{r\in\mathbb R:u_i(x_i^0+y_i-rg)\ge u_i(x_i^0)\}.
--   $$
--   Then the market-clearing problem attains its maximum:
--   $$
--   \exists\bar x\in\mathbb R^{I\times J},\qquad
--   \sum_{i\in I}\bar x_i=0,\qquad
--   \forall y\in\mathbb R^{I\times J},\quad
--   \sum_{i\in I}y_i=0\ \Longrightarrow
--   \sum_{i\in I}D_i(y_i)\le\sum_{i\in I}D_i(\bar x_i).
--   $$
--
--   This companion theorem supplies existence of an optimal market-clearing trade, using the same exchange-economy model as the published convergence goal. It makes no assertion about uniqueness, supporting prices, or finiteness of the optimal value.
--
--   **Formalization Note** The predicates and indifference prices are imported unchanged from the published base Model. Utilities and objective values are extended real; concavity uses the convex hypograph, and recession directions use the characterization on p. 14. Initial endowments are unrestricted. If some $u_i(x_i^0)=-\infty$, that agent's indifference price is identically $+\infty$, and zero trades attain the extended-real maximum. For an empty agent set the empty trade vector solves the empty-sum problem. No finite-utility or nonemptiness premise is added.
--
--   Differences from the source:
--   - encoding: Finite sets I of agents and J of assets; portfolios in ℝ^J. → Arbitrary finite types I and J with decidable equality; portfolios J → ℝ; empty index sets are permitted.; reason: Finite sums use Fintype instances; decidable equality is computational structure. Empty cases also satisfy the existence conclusion, so no nonemptiness premise is needed.
--   - reading: Problem (P) admits solutions under Assumptions 1 and 3. → There exists xbar satisfying the published SolvesP u g x0 xbar, using EReal objective comparisons even for off-domain initial endowments.; reason: The statement asks for global maximizers, not a finite optimum or a price. Equations (P) and (1), pp. 7–8, specify the full objective and trade domain; p. 9 permits short positions.
-- source:
--   T. Pennanen, Efficient allocations in double auction markets, arXiv:2001.02071v2, p. 14, Theorem 10; governing context: (P), p. 7; (1) and Assumption 1, p. 8; dom u_i, p. 9; Assumption 3, p. 14.

import Mathlib
import Definitions.Def_DoubleAuctionEff_Repeated_Model

namespace DoubleAuctionEff.Repeated.Supplement

theorem theorem_10 {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J]
    (u : I → (J → ℝ) → EReal) (g : J → ℝ) (x0 : I → J → ℝ)
    (h1 : ∀ i, Assumption1 (u i) g) (h3 : Assumption3 u) :
    ∃ xbar : I → J → ℝ, SolvesP u g x0 xbar := by sorry

end DoubleAuctionEff.Repeated.Supplement
