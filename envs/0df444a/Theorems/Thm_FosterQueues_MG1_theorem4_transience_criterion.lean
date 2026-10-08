-- Prove2me | Theorems.Thm_FosterQueues_MG1_theorem4_transience_criterion
-- name    : FosterQueues.MG1.theorem4_transience_criterion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T02:20:39.455909+00:00
-- url     : https://prove2.me/theorems/d47ac9a7-51c0-403b-b8c8-41fcb5cef7c7
-- title:
--   Theorem 4 — transient iff (7) has a bounded nonconstant solution
-- statement:
--   Let $P=[p_{ij}]$ be the transition matrix of an irreducible, aperiodic Markov chain on $\{0,1,2,\dots\}$. The system is transient if and only if there is a bounded, nonconstant real sequence $(y_i)_{i\ge0}$ satisfying
--   $$
--   \sum_{j=0}^{\infty}p_{ij}\,y_j = y_i \qquad (i\ne0).
--   $$
--
--   The equations are imposed in every row except row $0$: a solution is a bounded function that is harmonic off the state $0$. This is Foster's transience criterion; in §3 it is applied with $y_j=\xi^j$, $\xi$ the root of Theorem 7, to show that the M/G/1 chain is transient when $\rho>1$.
--
--   **Formalization Note** The chain is irreducible and aperiodic by the paper's standing assumption (§1, p. 355). "Bounded" means $|y_i|\le C$ for one constant $C$ and all $i$; "nonconstant" means $y_i\ne y_j$ for some $i,j$. Since $y$ is bounded and each row of $P$ is a probability vector, each series converges, and the equation is stated as convergence of the series to $y_i$. Transience means every state is returned to with probability less than one.
-- source:
--   Foster (Ann. Math. Statist. 24, 1953), Theorem 4, pp. 356–357, eq. (7)

import Mathlib
import Definitions.Def_FosterQueues_MG1_Model

open scoped ENNReal
open QueueingFundamentals.Foundations

namespace FosterQueues.MG1

/-- Foster (1953), Theorem 4, pp. 356–357: an irreducible aperiodic system is transient if and only
if the equations `∑_j p_ij y_j = y_i` (`i ≠ 0`) have a bounded nonconstant solution. The
equation is not imposed in row `0`. -/
theorem theorem4_transience_criterion (P : TransitionMatrix) (hirr : P.Irreducible)
    (hap : P.Aperiodic) :
    IsTransient P ↔
      ∃ y : ℕ → ℝ, (∃ C : ℝ, ∀ i, |y i| ≤ C) ∧ (∃ i j : ℕ, y i ≠ y j) ∧
        ∀ i : ℕ, i ≠ 0 → HasSum (fun j => P.p i j * y j) (y i) := by sorry

end FosterQueues.MG1
