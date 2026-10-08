-- Prove2me | Theorems.Thm_AdWordsMSVV_LowerBound_opt_round_instance
-- name    : AdWordsMSVV.LowerBound.opt_round_instance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:30:54.24098+00:00
-- url     : https://prove2.me/theorems/fe7cbf80-2043-4ef1-ba70-86d0100c1a23
-- title:
--   Proof of Theorem 9, p. 15 — the optimal allocation of every permuted instance is N (N·B after scaling), attained by Q_i ↦ π(i)
-- statement:
--   Let $N, B$ be natural numbers and $\pi$ a permutation of the $N$ bidders. On the permuted round instance $I_\pi$ (budget $B$, $N$ rounds of $B$ queries, round $Q_i$ bid on by $\pi(i),\dots,\pi(N)$), the allocation $\tau_\pi$ that sends every query of $Q_i$ to bidder $\pi(i)$ has offline revenue $NB$, and no allocation earns more:
--   $$\mathrm{rev}_B(I_\pi,\tau_\pi) = NB, \qquad \mathrm{rev}_B(I_\pi,\tau) \le NB \ \text{ for every allocation } \tau.$$
--
--   In the paper's units (budget $1$, bids $\epsilon = 1/B$) the optimum is $N$. This fixes the denominator of the competitive ratio in Theorem 9.
-- source:
--   Mehta, Saberi, Vazirani, Vazirani, AdWords and generalized on-line matching, J. ACM (2007), DOI 10.1145/1284320.1284321, p. 15, proof of Theorem 9, second paragraph

import Mathlib
import Definitions.Def_AdWordsMSVV_LowerBound_Setting

namespace AdWordsMSVV.LowerBound

theorem opt_round_instance (N B : ℕ) (π : Equiv.Perm (Fin N)) :
    offlineRevenue B (roundInstance N B π) (roundAllocation N B π) = N * B ∧
    ∀ τ : Fin (N * B) → Option (Fin N), offlineRevenue B (roundInstance N B π) τ ≤ N * B := by sorry

end AdWordsMSVV.LowerBound
