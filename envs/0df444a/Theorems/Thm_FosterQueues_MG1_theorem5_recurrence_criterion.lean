-- Prove2me | Theorems.Thm_FosterQueues_MG1_theorem5_recurrence_criterion
-- name    : FosterQueues.MG1.theorem5_recurrence_criterion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T02:20:25.694641+00:00
-- url     : https://prove2.me/theorems/2bc5ac8f-2452-42cf-ad46-1a729dad81fd
-- title:
--   Theorem 5 — a solution of (9) tending to infinity makes the system recurrent
-- statement:
--   Let $P=[p_{ij}]$ be the transition matrix of an irreducible, aperiodic Markov chain on $\{0,1,2,\dots\}$. Suppose there is a real sequence $(y_i)_{i\ge0}$ such that for every $i\ne0$ the series $\sum_j p_{ij}y_j$ converges and
--   $$
--   \sum_{j=0}^{\infty}p_{ij}\,y_j\le y_i \qquad (i\ne0),
--   $$
--   and $y_i\to\infty$ as $i\to\infty$. Then the system is recurrent: every state is returned to with probability one.
--
--   This is the recurrence half of Foster's criteria; it does not distinguish recurrent-null from recurrent-nonnull systems. In §3 it is applied with $y_j=j$ to show that the M/G/1 chain is recurrent when $\rho\le1$.
--
--   **Formalization Note** The chain is irreducible and aperiodic by the paper's standing assumption (§1, p. 355). The convergence of each series $\sum_j p_{ij}y_j$, $i\ne0$, is implicit in the inequality on the page and is stated as a hypothesis; the sequence $y$ is not assumed nonnegative, and nothing is imposed in row $0$.
-- source:
--   Foster (Ann. Math. Statist. 24, 1953), Theorem 5, p. 357, eq. (9)

import Mathlib
import Definitions.Def_FosterQueues_MG1_Model

open scoped ENNReal
open QueueingFundamentals.Foundations

namespace FosterQueues.MG1

/-- Foster (1953), Theorem 5, p. 357: an irreducible aperiodic system is recurrent if there is a
real sequence `y` with `∑_j p_ij y_j ≤ y_i` (the series converging) for every `i ≠ 0` and
`y_i → ∞` as `i → ∞`. -/
theorem theorem5_recurrence_criterion (P : TransitionMatrix) (hirr : P.Irreducible)
    (hap : P.Aperiodic) (y : ℕ → ℝ)
    (hsum : ∀ i : ℕ, i ≠ 0 → Summable (fun j => P.p i j * y j))
    (hineq : ∀ i : ℕ, i ≠ 0 → ∑' j : ℕ, P.p i j * y j ≤ y i)
    (hlim : Filter.Tendsto y Filter.atTop Filter.atTop) :
    IsRecurrent P := by sorry

end FosterQueues.MG1
