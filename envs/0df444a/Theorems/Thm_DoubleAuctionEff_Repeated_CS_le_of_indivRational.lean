-- Prove2me | Theorems.Thm_DoubleAuctionEff_Repeated_CS_le_of_indivRational
-- name    : DoubleAuctionEff.Repeated.CS_le_of_indivRational
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:22:01.303988+00:00
-- url     : https://prove2.me/theorems/09dccf21-74a8-42a5-8b68-7e3e6c9a1107
-- title:
--   Proof of Theorem 16, p. 19 — the market value CS does not increase along feasible individually rational reallocations
-- statement:
--   Let $I$ be a finite nonempty set of agents with utilities $u_i$ and numeraire $g$. If two allocations $x,y\in\mathbb R^{I\times J}$ have the same totals and $y$ is individually rational relative to $x$,
--   $$\sum_{i\in I}y_i=\sum_{i\in I}x_i,\qquad u_i(y_i)\ge u_i(x_i)\ \ (i\in I),$$
--   then
--   $$CS(y)\le CS(x),$$
--   where $CS(x)$ is the optimum value of the market clearing problem (P) with indifference prices built from $x$.
--
--   By Lemma 9 the constraints of (P′) at $y$ are more restrictive than at $x$. In the proof of Theorem 16 this gives that $CS(x^t)$ is nonincreasing along the repeated auction and that $CS(\bar x)\le CS(x^t)$ at a cluster point $\bar x$.
--
--   **Formalization Note** The paper states this step for consecutive iterates and again for a cluster point; the milestone states the common fact for arbitrary pairs of allocations.
-- source:
--   T. Pennanen, Efficient allocations in double auction markets, arXiv:2001.02071v2, p. 19, proof of Theorem 16 ('Thus, the constraints become more restrictive with t so the optimum value CS(x^t) is nonincreasing'; also 'by Lemma 9, CS(x̄) ≤ CS(x^t) for all t')

import Mathlib
import Definitions.Def_DoubleAuctionEff_Repeated_Model

namespace DoubleAuctionEff.Repeated
theorem CS_le_of_indivRational {I J : Type*} [Fintype I] [DecidableEq I] [Nonempty I] [Fintype J] [DecidableEq J] (u : I → (J → ℝ) → EReal) (g : J → ℝ) (x y : I → J → ℝ) (hsum : ∑ i, y i = ∑ i, x i) (hu : ∀ i, u i (x i) ≤ u i (y i)) : CS u g y ≤ CS u g x := by sorry
end DoubleAuctionEff.Repeated
