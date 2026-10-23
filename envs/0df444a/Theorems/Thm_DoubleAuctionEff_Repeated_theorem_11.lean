-- Prove2me | Theorems.Thm_DoubleAuctionEff_Repeated_theorem_11
-- name    : DoubleAuctionEff.Repeated.theorem_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:22:06.445118+00:00
-- url     : https://prove2.me/theorems/68afb6e7-29d8-4607-936f-9631fa4b6f87
-- title:
--   Theorem 11, p. 15 — under Assumption 1, Pareto allocations are double auction equilibria; the converse holds under Assumption 4
-- statement:
--   Let $I$ be a finite nonempty set of agents whose utilities $u_i$ satisfy Assumption 1, and let $g$ be the numeraire. For an allocation $x$, take $x$ itself as the endowment, so that feasibility means $\sum_ix'_i=\sum_ix_i$ and $CS(x)$ is the optimum value of (P) at $x$.
--
--   1. If $x_i\in\operatorname{dom}u_i$ for all $i$ and $x$ is Pareto efficient, then $x$ is a double auction equilibrium: $CS(x)=0$.
--   2. If every $u_i$ satisfies Assumption 4 and $CS(x)=0$, then $x$ is Pareto efficient.
--
--   This is the analogue, for the double auction mechanism, of the fundamental theorems of welfare economics.
--
--   **Formalization Note** In part 1 the hypothesis $x_i\in\operatorname{dom}u_i$ is added: with two agents, one good and $u_i=\log$ on $(0,\infty)$, the allocation $(0,e)$ is Pareto efficient but $CS=+\infty$, since an agent with utility $-\infty$ would pay any price. Part 2 needs no addition.
-- source:
--   T. Pennanen, Efficient allocations in double auction markets, arXiv:2001.02071v2, p. 15, Theorem 11 and Assumption 4; Pareto efficiency defined on p. 15

import Mathlib
import Definitions.Def_DoubleAuctionEff_Repeated_Model

namespace DoubleAuctionEff.Repeated
theorem theorem_11 {I J : Type*} [Fintype I] [DecidableEq I] [Nonempty I] [Fintype J] [DecidableEq J] (u : I → (J → ℝ) → EReal) (g : J → ℝ) (h1 : ∀ i, Assumption1 (u i) g) : (∀ x : I → J → ℝ, (∀ i, x i ∈ dom (u i)) → IsParetoEfficient u x x → IsDAEquilibrium u g x) ∧ ((∀ i, Assumption4 (u i) g) → ∀ x : I → J → ℝ, IsDAEquilibrium u g x → IsParetoEfficient u x x) := by sorry
end DoubleAuctionEff.Repeated
