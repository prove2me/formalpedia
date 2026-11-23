-- Prove2me | Theorems.Thm_BayesGroupHard_VertexCover_Supplement_theorem_2
-- name    : BayesGroupHard.VertexCover.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T11:48:20.735475+00:00
-- url     : https://prove2.me/theorems/86f99d5d-04fb-4e0a-87be-eed740053fc6
-- title:
--   Theorem 2, p. 11 — GROUP-DECISION with revealed beliefs is NP-hard; at t = 2 it is NP-hard to tell µ_i,2(1) ≤ exp(−Ω(n)) from µ_i,2(0) ≤ exp(−Ω(n))
-- statement:
--   **Theorem 2 (Approximating Beliefs).** Consider GROUP-DECISION in the revealed belief model with uniform priors, binary states $\Theta=\{0,1\}$ and binary private signals: given a network, rational signal structures, an agent $i$ with her signal, and the beliefs her neighbours reported at times $0$ and $1$, determine her posterior $\mu_{i,2}$. Write $n$ for the number of agents of an instance.
--
--   1. The problem is NP-hard: the language of codes of valid instances with $\mu_{i,2}(1)<\mu_{i,2}(0)$ is NP-hard under polynomial-time many-one reductions.
--   2. There is a constant $c>0$ such that, for every threshold $N$, it is NP-hard to distinguish the valid instances with at least $N$ agents and
--   $$\mu_{i,2}(1)\le e^{-cn}$$
--   from the valid instances with at least $N$ agents and
--   $$\mu_{i,2}(0)\le e^{-cn}:$$
--   every NP language reduces in polynomial time to this pair, its members landing in the first class and its non-members in the second.
--
--   Remark 1 of the paper reads this as a strong hardness of approximation: a computationally bounded agent cannot tell whether $\theta=0$ or $\theta=1$ almost surely. The theorem is unconditional; no hardness of RXC3 is assumed.
--
--   **Formalization Note.** NP, polynomial-time computability and reductions are the platform's `CookPvsNP` definitions (one-tape Turing machines), with `KingTerrain.NPHard.IsNPHard` for the first clause and `MeanBudgetXC.Supplement.PromiseNPHard` for the second. Instances, their binary code and validity are `BayesGroupHard.VertexCover.Supplement.Decision`.
--
--   Differences from the source:
--   - reading: "determine the Bayesian posterior belief µ_i,t" (a function problem) is NP-hard → NP-hardness of the decision language {valid t = 2 instances with µ_i,2(1) < µ_i,2(0)}; reason: any algorithm computing the posterior decides this language, and the paper's reduction separates the two cases this way.
--   - reading: "for a network of n agents at t = 2, NP-hard to distinguish µ_i,2(0) ≤ exp(−Ω(n)) and µ_i,2(1) ≤ exp(−Ω(n))" → ∃ c > 0, ∀ N, PromiseNPHard of the two sides with at least N agents, members of the NP language mapped to the µ_i,2(1)-small side; reason: Ω(n) with c fixed before the instance and the bound required for all large n; the sides shrink as N grows, so "for every N" equals "for all sufficiently large N", and for large N the sides are disjoint, which rules out the trivial reduction to an instance in both; the orientation is that of Appendix B (YES instances of RXC3 give small µ_i,2(1)).
--   - encoding: inputs → rational signal probabilities in [0,1] and rational reports, coded in binary, time fixed to t = 2, validity = positive probability of the history; reason: the paper does not fix an encoding; hardness of this restriction of the input format is hardness of the problem, and every instance of the paper's reduction is of this form.
-- source:
--   Hązła, Jadbabaie, Mossel & Rahimian, Bayesian Decision Making in Groups is Hard, arXiv:1705.04770v4, p. 11, Theorem 2; Problem 2 p. 8; proof in Appendix B pp. 31–33

import Mathlib
import Definitions.Def_BayesGroupHard_VertexCover_Supplement_Decision

namespace BayesGroupHard.VertexCover.Supplement

/-- Theorem 2, p. 11 (Approximating Beliefs): GROUP-DECISION with revealed beliefs, uniform prior,
binary states and binary signals is NP-hard (its decision version "is state 0 strictly more
likely than state 1 at t = 2" is NP-hard); and there is `c > 0` such that, for every threshold
`N` on the number of agents, it is NP-hard to distinguish instances with
`µ_i,2(1) ≤ exp(-c·#agents)` from instances with `µ_i,2(0) ≤ exp(-c·#agents)`. -/
theorem theorem_2 :
    KingTerrain.NPHard.IsNPHard decisionLanguage ∧
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ,
      MeanBudgetXC.Supplement.PromiseNPHard (smallBelief true c N) (smallBelief false c N) := by sorry

end BayesGroupHard.VertexCover.Supplement
