-- Prove2me | Theorems.Thm_DoubleAuctionEff_Repeated_theorem_4
-- name    : DoubleAuctionEff.Repeated.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:22:02.404296+00:00
-- url     : https://prove2.me/theorems/e4b763b0-a9db-467e-a912-3dd5883c4404
-- title:
--   Theorem 4, p. 11 — under Assumption 2, x̄ solves the market clearing problem (P) iff a price p is a supergradient of every D_i at x̄_i and Σ_i x̄_i = 0
-- statement:
--   Consider agents $i\in I$ (finite, nonempty) with utilities $u_i$ satisfying Assumption 1, endowments $x^0_i$, numeraire $g$, and indifference prices $D_i$ built from $x^0_i$. Suppose Assumption 2 holds: for some $\varepsilon>0$ the optimum value of
--   $$\text{maximize }\sum_{i\in I}D_i(x_i)\ \text{ over }x\in\mathbb R^{I\times J}\ \text{ subject to }\sum_{i\in I}x_i=z \qquad (P_z)$$
--   is finite whenever $\|z\|\le\varepsilon$. Then $\bar x$ solves the market clearing problem (P) $=(P_0)$ if and only if there is a price vector $p\in\mathbb R^J$ with
--   $$p\in\partial D_i(\bar x_i)\ \ \forall i\in I,\qquad \sum_{i\in I}\bar x_i=0,$$
--   where $p\in\partial D_i(\bar x_i)$ means that $D_i(\bar x_i)$ is finite and $D_i(x_i)\le D_i(\bar x_i)+p\cdot(x_i-\bar x_i)$ for all $x_i$.
--
--   The price $p$ is the market clearing price of the double auction: every agent trades at the common linear price $p$.
--
--   **Formalization Note** Assumption 1 is the paper's standing assumption and is stated explicitly. $|z|$ is the sup norm on $\mathbb R^J$; any norm yields the same Assumption 2.
-- source:
--   T. Pennanen, Efficient allocations in double auction markets, arXiv:2001.02071v2, p. 11, Theorem 4 with (2)–(4) and Assumption 2; (P_z) on p. 10

import Mathlib
import Definitions.Def_DoubleAuctionEff_Repeated_Model

open Matrix

namespace DoubleAuctionEff.Repeated
theorem theorem_4 {I J : Type*} [Fintype I] [DecidableEq I] [Nonempty I] [Fintype J] [DecidableEq J] (u : I → (J → ℝ) → EReal) (g : J → ℝ) (x0 : I → J → ℝ) (h1 : ∀ i, Assumption1 (u i) g) (h2 : Assumption2 u g x0) (xbar : I → J → ℝ) : SolvesP u g x0 xbar ↔ ∃ p : J → ℝ, (∀ i, IsSupergrad (indiffPrice (u i) g (x0 i)) (xbar i) p) ∧ ∑ i, xbar i = 0 := by sorry
end DoubleAuctionEff.Repeated
