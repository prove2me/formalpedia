-- Prove2me | Theorems.Thm_AdaptSubCover_Rounds_theorem_3_1
-- name    : AdaptSubCover.Rounds.theorem_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:18:40.20687+00:00
-- url     : https://prove2.me/theorems/2eb3bd04-311d-47b5-9fa9-0064a6fc5d65
-- title:
--   Theorem 3.1, p. 7 — ParCA solves partial cover non-adaptively at cost O(ln(1/δ)/δ) times the optimal adaptive full-cover cost
-- statement:
--   There is an absolute constant $C > 0$ such that the following holds for every instance of stochastic submodular cover with independent items that some feasible adaptive solution covers, with $Q > 0$, and every $\delta = 2^{-z}$, $z \in \mathbb N$. A greedy list $L$ of ParCA exists, and for every such list the non-adaptive strategy $\mathtt{NA}$ (probe $L$ in order until $f(R) > \tau = Q(1-\delta)$)
--
--   1. solves the partial cover problem: almost surely its realization $R$ satisfies $f(R) > Q(1-\delta)$;
--   2. has expected cost at most
--   $$\mathbb E[\mathtt{NA}] \;\le\; C\cdot\frac{1 + \ln(1/\delta)}{\delta}\cdot \mathbb E[\mathtt{OPT}]$$
--   for every feasible adaptive solution $\mathtt{OPT}$ of the full cover problem.
--
--   This is the single-round building block of the $r$-round algorithm.
--
--   **Formalization Note.** The paper's $O(\ln(1/\delta)/\delta)$ is read as $C(1 + \ln(1/\delta))/\delta$: the printed expression vanishes at $\delta = 1$, and the two agree up to a constant for $\delta \le 1/2$. $\delta$ is a power of two, as in the analysis (p. 10). $Q > 0$ is assumed: for $Q = 0$ the partial cover target $f(R) > 0$ is unattainable. Feasibility of the instance is assumed; without it the right-hand side has no meaning.
-- source:
--   Ghuge, Gupta, Nagarajan, The Power of Adaptivity for Stochastic Submodular Cover, arXiv:2106.16115v1, p. 7, Theorem 3.1 (proof pp. 10, 15)

import Mathlib
import Definitions.Def_AdaptSubCover_Rounds_ParCA

namespace AdaptSubCover.Rounds

theorem theorem_3_1 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (U : Type) [Fintype U] [DecidableEq U] (m : ℕ) (I : Instance U m),
        I.Standing → 0 < I.Q → (∃ π : AdaptivePolicy m U, I.Feasible π) → ∀ z : ℕ,
          (∃ L : List (Fin m), I.IsGreedyList (fun A => (I.f A : ℝ)) I.Q (I.tau z) Finset.univ L) ∧
          ∀ L : List (Fin m), I.IsGreedyList (fun A => (I.f A : ℝ)) I.Q (I.tau z) Finset.univ L →
            (∀ ω, 0 < I.prob ω → I.tau z < (I.f (I.NA (I.tau z) L ω).realized : ℝ)) ∧
            ∀ π : AdaptivePolicy m U, I.Feasible π →
              I.E (fun ω => (I.costOf (I.NA (I.tau z) L ω) : ℝ)) ≤
                C * ((1 + Real.log (1 / delta z)) / delta z) * I.expCost π := by sorry

end AdaptSubCover.Rounds
