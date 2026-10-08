-- Prove2me | Theorems.Thm_FosterQueues_GIM1_theorem1_sufficient
-- name    : FosterQueues.GIM1.theorem1_sufficient
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T04:58:20.187849+00:00
-- url     : https://prove2.me/theorems/1ab331a2-c502-472e-a8f5-7ff7aa50ced7
-- title:
--   Theorem 1 (sufficiency) — a nonnull absolutely summable solution of x = xP makes the system ergodic
-- statement:
--   Let $[p_{ij}]$ ($i, j = 0, 1, 2, \dots$) be the transition matrix of an irreducible, aperiodic Markov chain (the "system"). Suppose there is a real sequence $(x_i)_{i \ge 0}$, not identically zero, with $\sum_i |x_i| < \infty$, solving
--   $$
--   \sum_{i=0}^{\infty} x_i\, p_{ij} = x_j \qquad (j = 0, 1, 2, \dots). \tag{1}
--   $$
--   Then the system is ergodic, i.e. positive recurrent: every state $j$ is recurrent ($f_{jj} = 1$) and has a finite mean recurrence time.
--
--   This is the sufficiency half of Foster's Theorem 1. It is the criterion used to prove that the GI/M/1 chain is ergodic when $\rho < 1$, with $x_i = \xi^i$.
--
--   **Formalization Note** The $x_i$ may take either sign, as in the paper; only "nonnull" (some $x_i \ne 0$) and absolute summability are assumed. Irreducibility and aperiodicity are the paper's standing assumptions (§1, p. 355) and are hypotheses here. "Ergodic" (recurrent-nonnull) is the published predicate `PositiveRecurrent`. The equations (1) are stated with `HasSum`, i.e. each series converges to $x_j$.
-- source:
--   Foster (Ann. Math. Statist. 24, 1953), Theorem 1 (first half), p. 355; standing assumptions §1, p. 355

import Mathlib
import Definitions.Def_QueueingFundamentals_Foundations_MarkovChain
import Definitions.Def_FosterQueues_GIM1_Model

open scoped ENNReal
open QueueingFundamentals.Foundations

namespace FosterQueues.GIM1

theorem theorem1_sufficient (P : TransitionMatrix) (hirr : P.Irreducible) (hap : P.Aperiodic)
    (x : ℕ → ℝ) (hnonnull : ∃ i, x i ≠ 0) (habs : Summable (fun i => |x i|))
    (heq : ∀ j, HasSum (fun i => x i * P.p i j) (x j)) :
    P.PositiveRecurrent := by sorry

end FosterQueues.GIM1
