-- Prove2me | Theorems.Thm_ArapostathisAC_RossRecurrence_theorem_2_1_iii
-- name    : ArapostathisAC.RossRecurrence.theorem_2_1_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:07:16.119391+00:00
-- url     : https://prove2.me/theorems/9a5cadd7-1984-43a1-8f08-e90db7af9480
-- title:
--   Theorem 2.1 (iii) — a β-discount optimal stationary deterministic policy exists
-- statement:
--   Consider the countable-state controlled Markov process of §5: state space $S=\{0,1,2,\dots\}$, nonempty compact admissible action sets $U(i)$, a nonnegative cost $c(i,\cdot)$ and transition probabilities $P(j\mid i,\cdot)$ that are continuous on $U(i)$. For $\beta\in(0,1)$, let $J_\beta(i,\pi)$ be the expected $\beta$-discounted cost of the policy $\pi$ from state $i$, and let $J^*_\beta(i)=\inf_{\pi\in\Pi}J_\beta(i,\pi)$, where $\Pi$ is the class of all admissible policies.
--
--   **Theorem 2.1 (iii).** For every $\beta\in(0,1)$ there is a stationary deterministic policy $f\in\Pi_{SD}$ that is $\beta$-discount optimal:
--   $$J_\beta(i,f)=J^*_\beta(i)\qquad\text{for every } i\in S.$$
--
--   The proof of Theorem 5.3 starts from such a policy $f_\beta$.
--
--   **Formalization Note.** The paper states Theorem 2.1 for Borel models under Assumptions 2.1–2.3: nonnegative cost, weakly continuous transitions, an upper semicontinuous $U$ and a lower semicontinuous cost. With a countable discrete state space these assumptions follow from the §5 standing assumptions built into the model: compact $U(i)$ and continuity of $c(i,\cdot)$ and $P(j\mid i,\cdot)$. The survey cites this result and does not prove it (Remark 2.2). No bound on $c$ is assumed. $J^*_\beta$ is computed in $[0,\infty]$, and the infimum is over all history-dependent randomized admissible policies.
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), p. 289, Theorem 2.1 (iii)

import Mathlib
import Definitions.Def_ArapostathisAC_RossRecurrence_CMP
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ArapostathisAC.RossRecurrence

/-- Theorem 2.1 (iii) (p. 289) in the countable-state model of §5: for every discount factor
`β ∈ (0, 1)` a `β`-discount optimal stationary deterministic policy exists. -/
theorem theorem_2_1_iii {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : CMP A) (β : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ f : StationaryPolicy M, IsDiscOptimal M f β := by sorry

end ArapostathisAC.RossRecurrence
