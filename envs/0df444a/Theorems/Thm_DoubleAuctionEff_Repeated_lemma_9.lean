-- Prove2me | Theorems.Thm_DoubleAuctionEff_Repeated_lemma_9
-- name    : DoubleAuctionEff.Repeated.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:22:00.684031+00:00
-- url     : https://prove2.me/theorems/f7419bfe-6b2e-42f9-84da-fcd6fd584d78
-- title:
--   Lemma 9, p. 13 — the market clearing problem (P) and problem (P′) (maximize r s.t. Σ w_i + rg = Σ x^0_i, u_i(w_i) ≥ u_i(x^0_i)) have equal values and corresponding solutions
-- statement:
--   Let $I$ be a finite nonempty set of agents with utilities $u_i$, endowments $x^0_i$, numeraire $g$ and indifference prices $D_i$ at $x^0_i$. Consider
--   $$\text{maximize } r \text{ over } r\in\mathbb R,\ w\in\mathbb R^{I\times J}\ \text{ subject to } \sum_{i\in I}w_i+rg=\sum_{i\in I}x^0_i,\quad u_i(w_i)\ge u_i(x^0_i)\ \ (i\in I). \qquad (P')$$
--
--   1. The optimum value $CS(x^0)$ of (P) equals the optimum value of (P′), $\sup\{r\mid \exists w \text{ feasible}\}$ (both in $[-\infty,+\infty]$).
--   2. If every $u_i$ satisfies Assumption 1, then for every $\bar x$: $\bar x$ solves (P) and $CS(x^0)<+\infty$ if and only if there are $r_i\in\mathbb R$ such that $(r,w)$ with
--   $$r=\sum_{i\in I}r_i,\qquad w_i=x^0_i+\bar x_i-r_ig$$
--   solves (P′).
--
--   The lemma rewrites the market clearing problem directly in terms of utilities, which is how the monotonicity of the surplus along the repeated auction and the welfare theorem are obtained.
--
--   **Formalization Note** Part 2 adds the finiteness $CS(x^0)<+\infty$: when the optimum value of (P) is $+\infty$, (P) may have a maximizer (with value $+\infty$) while (P′), whose objective is real, has none. Part 1 needs no assumption.
-- source:
--   T. Pennanen, Efficient allocations in double auction markets, arXiv:2001.02071v2, p. 13, Lemma 9 and problem (P′)

import Mathlib
import Definitions.Def_DoubleAuctionEff_Repeated_Model

namespace DoubleAuctionEff.Repeated
theorem lemma_9 {I J : Type*} [Fintype I] [DecidableEq I] [Nonempty I] [Fintype J] [DecidableEq J] (u : I → (J → ℝ) → EReal) (g : J → ℝ) (x0 : I → J → ℝ) : CS u g x0 = (⨆ (r : ℝ) (_ : ∃ w : I → J → ℝ, FeasibleP' u g x0 r w), (r : EReal)) ∧ ((∀ i, Assumption1 (u i) g) → ∀ xbar : I → J → ℝ, (SolvesP u g x0 xbar ∧ CS u g x0 ≠ ⊤) ↔ ∃ r : I → ℝ, SolvesP' u g x0 (∑ i, r i) (fun i => x0 i + xbar i - r i • g)) := by sorry
end DoubleAuctionEff.Repeated
