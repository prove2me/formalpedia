-- Prove2me | Theorems.Thm_BayesGroupHard_VertexCover_Supplement_theorem_1
-- name    : BayesGroupHard.VertexCover.Supplement.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T11:50:42.585381+00:00
-- url     : https://prove2.me/theorems/8ded07d9-d731-4979-9f42-2b8593a83de6
-- title:
--   Theorem 1, p. 9 — GROUP-DECISION in the binary action model is NP-hard at t = 2; it is NP-hard to tell µ_i,2(0) < exp(−Ω(n)) from µ_i,2(1) < exp(−Ω(n))
-- statement:
--   **Theorem 1 (Binary Action Model).** Consider GROUP-DECISION in the binary action model (uniform prior, binary states and binary private signals, every agent announcing her MAP estimate of $\theta$ with ties to $0$): given a network, rational signal structures, an agent $i$ with her signal, and the actions her neighbours took at times $0$ and $1$, determine her Bayesian action $a_{i,2}$. Write $n$ for the number of agents of an instance.
--
--   1. The problem is NP-hard at $t=2$: the language of codes of valid instances with $a_{i,2}=0$ is NP-hard under polynomial-time many-one reductions.
--   2. There is a constant $c>0$ such that, for every threshold $N$, it is NP-hard to distinguish the valid instances with at least $N$ agents and
--   $$\mu_{i,2}(1)< e^{-cn}$$
--   from the valid instances with at least $N$ agents and
--   $$\mu_{i,2}(0)< e^{-cn}:$$
--   every NP language reduces in polynomial time to this pair, its members landing in the first class and its non-members in the second.
--
--   Remark 1 of the paper reads this as a strong hardness of approximation: a computationally bounded agent cannot tell whether $\theta=0$ or $\theta=1$ almost surely. The theorem is unconditional; neither the hardness of approximating vertex cover (the paper's Theorem 5, Khot et al. 2018) nor anything else is assumed. Its belief content for the paper's reduction is Theorem 6, the goal of this mission.
--
--   **Formalization Note.** NP, polynomial-time computability and reductions are the platform's `CookPvsNP` definitions (one-tape Turing machines), with `KingTerrain.NPHard.IsNPHard` for the first clause and `MeanBudgetXC.Supplement.PromiseNPHard` for the second. Instances, their binary code and validity are `BayesGroupHard.VertexCover.Supplement.BinaryDecision`.
--
--   Differences from the source:
--   - reading: "the GROUP-DECISION problem in the binary action model is NP-hard at t = 2" (determine a_i,2) → NP-hardness of the decision language {valid t = 2 instances with a_i,2 = 0}; reason: a_i,2 is a bit, so computing it is deciding this language; the orientation (a_i,2 = 0) is the one the paper's reduction gives (small vertex covers force µ_i,2(1) small, Theorem 6).
--   - reading: "for a network of n agents, NP-hard to distinguish µ_i,2(0) < exp(−Ω(n)) and µ_i,2(1) < exp(−Ω(n))" → ∃ c > 0, ∀ N, PromiseNPHard of the two sides with at least N agents, members of the NP language mapped to the µ_i,2(1)-small side; reason: Ω(n) with c fixed before the instance and the bound required for all large n; the sides shrink as N grows, so "for every N" equals "for all sufficiently large N", and for large N the sides are disjoint, which rules out the trivial reduction to an instance in both; the orientation is that of Appendix A (YES instances of gap vertex cover give small µ_i,2(1)).
--   - encoding: inputs → rational signal probabilities in [0,1] and binary actions, coded in binary, time fixed to t = 2, validity = positive probability of the history; reason: the paper does not fix an encoding; hardness of this restriction of the input format is hardness of the problem. The paper's own reduction (Theorem 6, (9)) gives agent κ an irrational signal structure ("efficiently computable numbers"); its proof has a Θ(n) margin on both sides of λ_κ(0) ((13), (18)), so a rational κ within O(1) of it gives the same conclusion.
-- source:
--   Hązła, Jadbabaie, Mossel & Rahimian, Bayesian Decision Making in Groups is Hard, arXiv:1705.04770v4, p. 9, Theorem 1; Problem 1 p. 7; proof in Appendix A pp. 27–30 (Theorem 6 with Theorem 5)

import Mathlib
import Definitions.Def_BayesGroupHard_VertexCover_Supplement_BinaryDecision

namespace BayesGroupHard.VertexCover.Supplement

/-- Theorem 1, p. 9 (Binary Action Model): GROUP-DECISION in the binary action model is NP-hard
at t = 2 (its decision version "is the Bayesian action a_{i,2} equal to 0" is NP-hard); and there
is `c > 0` such that, for every threshold `N` on the number of agents, it is NP-hard to
distinguish instances with `µ_i,2(1) < exp(-c·#agents)` from instances with
`µ_i,2(0) < exp(-c·#agents)`. -/
theorem theorem_1 :
    KingTerrain.NPHard.IsNPHard binDecisionLanguage ∧
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ,
      MeanBudgetXC.Supplement.PromiseNPHard (binSmallBelief true c N) (binSmallBelief false c N) := by sorry

end BayesGroupHard.VertexCover.Supplement
