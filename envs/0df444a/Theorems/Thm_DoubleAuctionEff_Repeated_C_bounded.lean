-- Prove2me | Theorems.Thm_DoubleAuctionEff_Repeated_C_bounded
-- name    : DoubleAuctionEff.Repeated.C_bounded
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:22:03.260881+00:00
-- url     : https://prove2.me/theorems/f2db7502-6a39-47c6-8b95-0bce98bf99a4
-- title:
--   Proof of Theorem 16, pp. 18–19 — under Assumptions 1 and 3 the feasible individually rational allocations form a bounded set
-- statement:
--   Let $I$ be a finite nonempty set of agents whose utilities $u_i$ satisfy Assumption 1, let $x^0$ be an allocation with $x^0_i\in\operatorname{dom}u_i$ for all $i$, and suppose Assumption 3 holds: if $u_i^\infty(x_i)\ge0$ for all $i$ and $\sum_ix_i=0$ then $x=0$. Then the set
--   $$C=\Big\{x\in\mathbb R^{I\times J}\ \Big|\ \sum_{i\in I}x_i=\sum_{i\in I}x^0_i,\ u_i(x_i)\ge u_i(x^0_i)\ \ (i\in I)\Big\}$$
--   is bounded.
--
--   Since every iterate of the repeated auction lies in $C$, this is the first claim of Theorem 16.
--
--   **Formalization Note** The hypothesis $x^0_i\in\operatorname{dom}u_i$ is added: if $u_i(x^0_i)=-\infty$ the constraint of agent $i$ is void and $C$ can be unbounded. In Theorem 16 it follows from the hypotheses.
-- source:
--   T. Pennanen, Efficient allocations in double auction markets, arXiv:2001.02071v2, pp. 18–19, proof of Theorem 16 (the set C and its recession cone)

import Mathlib
import Definitions.Def_DoubleAuctionEff_Repeated_Model

namespace DoubleAuctionEff.Repeated
theorem C_bounded {I J : Type*} [Fintype I] [DecidableEq I] [Nonempty I] [Fintype J] [DecidableEq J] (u : I → (J → ℝ) → EReal) (g : J → ℝ) (x0 : I → J → ℝ) (h1 : ∀ i, Assumption1 (u i) g) (h3 : Assumption3 u) (hx0 : ∀ i, x0 i ∈ dom (u i)) : Bornology.IsBounded {x : I → J → ℝ | ∑ i, x i = ∑ i, x0 i ∧ ∀ i, u i (x0 i) ≤ u i (x i)} := by sorry
end DoubleAuctionEff.Repeated
