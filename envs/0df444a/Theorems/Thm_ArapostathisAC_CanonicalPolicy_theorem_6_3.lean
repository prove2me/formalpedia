-- Prove2me | Theorems.Thm_ArapostathisAC_CanonicalPolicy_theorem_6_3
-- name    : ArapostathisAC.CanonicalPolicy.theorem_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T07:42:47.129682+00:00
-- url     : https://prove2.me/theorems/62214c37-e9a1-493a-b6e4-2e9bc28cab36
-- title:
--   Theorem 6.3 (i)–(iii) — a canonical policy is strong average optimal and J(x, π*) = J*(x) = ρ(x)
-- statement:
--   Let $(S, A, U, P, c)$ be a discrete-time controlled Markov process with Borel state space $S$, Borel action space $A$, nonempty compact admissible action sets $U(x)$ with measurable graph $K$, transition kernel $P$, and measurable one-stage cost $c \ge 0$ that is bounded on $K$, i.e. $c \in \mathcal M_b(K)$. Let $(\rho, h, \pi^*)$ be a canonical triplet: $\rho, h \in \mathcal M_b(S)$, $\pi^* \in \Pi$ is an admissible (possibly randomized and history-dependent) policy, and
--   $$J_N(x, \pi^*, h) = J^*_N(x, h) = h(x) + N\rho(x) \qquad \forall N \in \mathbb N_0,\ x \in S.$$
--   Then, for each $x \in S$:
--   1. $J_N(x, \pi^*) \le J_N(x, \pi) + \operatorname{span}(h)$ for every $N \in \mathbb N_0$ and every $\pi \in \Pi$;
--   2. $\pi^*$ is strong average optimal: $\displaystyle\limsup_{N\to\infty} \tfrac1N J_N(x,\pi^*) \le \liminf_{N\to\infty}\tfrac1N J_N(x,\pi)$ for all $x \in S$ and $\pi \in \Pi$;
--   3. $$J(x, \pi^*) = J^*(x) = \rho(x),$$ where $J(x, \pi) = \limsup_N \frac1N J_N(x, \pi)$ and $J^*(x) = \inf_{\pi \in \Pi} J(x, \pi)$.
--
--   The theorem says that a canonical triplet solves the average-cost problem completely: $\rho$ is the optimal average cost from every initial state, and the canonical policy attains it in the strongest sense, its pessimistic long-run performance being no worse than the optimistic long-run performance of any competitor.
--
--   **Formalization Note.** $\Pi$ is the class of all admissible policies, randomized and history dependent; $\pi^*$ is not restricted to stationary policies. $J$, $J^*$ and both sides of (6.5) are computed in `EReal`, so (iii) is the two equalities $J(x,\pi^*) = J^*(x)$ and $J^*(x) = \rho(x)$ of extended reals. The theorem's further parts are posed separately: (v) as `theorem_6_3_v`, (vi) as `theorem_6_3_vi`; part (iv) is not posed, because its proof (p. 319) goes through Theorem 2.1 (iv) under Assumptions 2.1–2.3, which Theorem 6.3 does not assume.
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), p. 318, Theorem 6.3 (i)–(iii); definitions (6.4), (6.5) on p. 316

import Mathlib
import Definitions.Def_ArapostathisAC_CanonicalPolicy_CMP

open MeasureTheory ProbabilityTheory Filter Topology

namespace ArapostathisAC.CanonicalPolicy

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S]
  [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]

/-- Theorem 6.3 (i)–(iii), p. 318. Let `(ρ, h, π*)` be a canonical triplet and `c ∈ 𝓜_b(K)`.
Then, for each `x ∈ S`:
(i) `J_N(x, π*) ≤ J_N(x, π) + span(h)` for every `N` and every `π ∈ Π`;
(ii) `π*` is strong average optimal;
(iii) `J(x, π*) = J*(x) = ρ(x)`. -/
theorem theorem_6_3 (M : BorelCMP S A) (hc : CostBounded M) (ρ h : S → ℝ) (πs : Policy M)
    (hcan : IsCanonical M ρ h πs) :
    (∀ (x : S) (N : ℕ) (π : Policy M), JN0 M πs N x ≤ JN0 M π N x + span h) ∧
    IsStrongAvgOptimal M πs ∧
    (∀ x : S, avgCost M πs x = optAvg M x ∧ optAvg M x = (ρ x : EReal)) := by sorry

end ArapostathisAC.CanonicalPolicy
