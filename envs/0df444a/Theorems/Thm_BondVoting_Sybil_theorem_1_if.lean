-- Prove2me | Theorems.Thm_BondVoting_Sybil_theorem_1_if
-- name    : BondVoting.Sybil.theorem_1_if
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:52:49.895001+00:00
-- url     : https://prove2.me/theorems/acce3500-84cc-4f90-9ea2-1af73df421d2
-- title:
--   Theorem 1 (“if” direction), p. 14 — a payoff linear in the stake is Sybil resistant
-- statement:
--   Let $T > 0$ be the commitment horizon and $\pi(q, t)$ an agent's payoff function. Suppose that
--
--   1. for every $t \in (0, T]$ the payoff is linear in the stake: there are $\alpha, \beta$ (depending on $t$) with $\pi(q, t) = \alpha + \beta q$ for all $q \ge 0$;
--   2. $\pi(0, t) = 0$ for all $t$, and $\pi(q, 0) = 0$ for all $q$ (the boundary conditions of Assumption 1).
--
--   Then $\pi$ is Sybil resistant: for no budget $q > 0$, no number of identities $M$, and no stakes $q_1, \dots, q_M \ge 0$ with $\sum_m q_m \le q$ and commitments $t_1, \dots, t_M \in (0, T]$ is
--   $$\sum_{m=1}^{M} \pi(q_m, t_m) > \pi(q, t) \quad \text{for every } t \in [0, T].$$
--
--   This is the half of Theorem 1 that the paper applies to bond voting.
--
--   **Formalization Note.** Theorem 1 is stated "given Assumptions 1 and 2" for mechanisms with non-increasing influence of tokens; the proof of the "if" direction (p. 16) uses only linearity and the boundary conditions, so the curvature and continuity conditions of Assumption 1 and Definition 3 are not hypotheses here, which makes the statement stronger. (Bond voting itself violates Assumption 1's continuity at $t = 0$.) The "only if" direction is not part of this statement.
-- source:
--   Mohan, Khezr & Berg, Voting with time commitment for decentralized governance: Bond voting as a Sybil-resistant mechanism, SSRN 4259599 (PDF of 2024-02-20), p. 14, Theorem 1 (“if” direction), proof (b) p. 16

import Mathlib
import Definitions.Def_BondVoting_Sybil_Model

namespace BondVoting.Sybil
theorem theorem_1_if (π : ℝ → ℝ → ℝ) (T : ℝ) (hT : 0 < T)
    (hlin : ∀ t ∈ Set.Ioc 0 T, ∃ α β : ℝ, ∀ q : ℝ, 0 ≤ q → π q t = α + β * q)
    (h0 : ∀ t : ℝ, π 0 t = 0) (hq0 : ∀ q : ℝ, π q 0 = 0) :
    SybilResistant π T := by sorry
end BondVoting.Sybil
