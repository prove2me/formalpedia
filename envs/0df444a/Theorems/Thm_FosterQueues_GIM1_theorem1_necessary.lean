-- Prove2me | Theorems.Thm_FosterQueues_GIM1_theorem1_necessary
-- name    : FosterQueues.GIM1.theorem1_necessary
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T04:58:15.282474+00:00
-- url     : https://prove2.me/theorems/112193bc-b76f-4e06-aeee-8610dcb9dd2a
-- title:
--   Theorem 1 (necessity) — in an ergodic system every nonnegative solution of xP ≤ x is summable
-- statement:
--   Let $[p_{ij}]$ ($i, j = 0, 1, 2, \dots$) be the transition matrix of an irreducible, aperiodic Markov chain that is ergodic (positive recurrent). Let $(x_i)_{i\ge 0}$ be any nonnegative solution of the inequalities
--   $$
--   \sum_{i=0}^{\infty} x_i\, p_{ij} \le x_j \qquad (j = 0, 1, 2, \dots), \tag{2}
--   $$
--   where each series on the left converges. Then
--   $$
--   \sum_{i=0}^{\infty} x_i < \infty .
--   $$
--
--   This is the necessity half of Foster's Theorem 1. Contrapositively, a nonnegative solution of (2) with $\sum x_i = \infty$ shows that the system is not ergodic; for the GI/M/1 chain with $\rho \ge 1$ the paper applies it to $x_i \equiv 1$.
--
--   **Formalization Note** The convergence of every series in (2) is an explicit hypothesis: an inequality between infinite sums presupposes them, and without it a divergent series (which Lean evaluates to $0$) would satisfy (2) vacuously. The conclusion "$\sum x_i < \infty$" is summability of $x$. Irreducibility and aperiodicity are the paper's standing assumptions (§1, p. 355). The two halves of Theorem 1 have different conditions, so they are two theorems rather than one equivalence.
-- source:
--   Foster (Ann. Math. Statist. 24, 1953), Theorem 1 (second half), p. 355; standing assumptions §1, p. 355

import Mathlib
import Definitions.Def_QueueingFundamentals_Foundations_MarkovChain
import Definitions.Def_FosterQueues_GIM1_Model

open scoped ENNReal
open QueueingFundamentals.Foundations

namespace FosterQueues.GIM1

theorem theorem1_necessary (P : TransitionMatrix) (hirr : P.Irreducible) (hap : P.Aperiodic)
    (herg : P.PositiveRecurrent) (x : ℕ → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hsumm : ∀ j, Summable (fun i => x i * P.p i j))
    (hineq : ∀ j, ∑' i, x i * P.p i j ≤ x j) :
    Summable x := by sorry

end FosterQueues.GIM1
