-- Prove2me | Theorems.Thm_FosterQueues_MG1_mean_first_passage_linear
-- name    : FosterQueues.MG1.mean_first_passage_linear
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T02:20:30.641522+00:00
-- url     : https://prove2.me/theorems/07514ae4-ffdc-4bd7-831f-7eb884adfcd2
-- title:
--   §3 display — μ_{i,i−1} = μ₁₀ and μ_{i0} = iμ₁₀ for the ergodic M/G/1 chain
-- statement:
--   Let $k_0,k_1,\dots$ be positive numbers with $\sum_n k_n=1$, and let $P$ be the M/G/1 transition matrix built from them ($p_{0j}=k_j$; $p_{ij}=k_{j-i+1}$ for $i\ge1$, $j\ge i-1$; $p_{ij}=0$ otherwise). Write $\mu_{ij}$ for the mean first-passage time from state $i$ to state $j$. If the chain is ergodic (positive recurrent), then for every $i\ne0$
--   $$
--   \mu_{i,i-1}=\mu_{10}
--   \qquad\text{and}\qquad
--   \mu_{i0}=i\,\mu_{10}.
--   $$
--
--   The M/G/1 chain moves down by at most one state per step, and its rows from row $1$ on are shifts of one another; so the passage from $i$ to $0$ is a sum of $i$ passages, each one level down, with the same law. Combined with Theorem 3 this identity yields $\mu_{10}\rho=\mu_{10}-1$, hence $\rho<1$ for an ergodic M/G/1 chain.
--
--   **Formalization Note** Mean first-passage times take values in $[0,\infty]$ and the identity is stated there. Ergodicity is kept as a hypothesis, as in the paper, where the display sits inside the argument "suppose the system to be ergodic"; without recurrence the first-passage distributions can be defective and the additivity behind the identity can fail.
-- source:
--   Foster (Ann. Math. Statist. 24, 1953), §3, p. 358, display μ_{i0} = iμ_{10} (with μ_{i,i−1} = μ_{10})

import Mathlib
import Definitions.Def_FosterQueues_MG1_Model

open scoped ENNReal
open QueueingFundamentals.Foundations

namespace FosterQueues.MG1

/-- Foster (1953), §3, p. 358: for the ergodic M/G/1 system, `μ_{i,i-1} = μ_{10}` and
`μ_{i0} = i μ_{10}` for every `i ≠ 0`, where `μ_ij` is the mean first-passage time from `i`
to `j`. -/
theorem mean_first_passage_linear (k : ℕ → ℝ) (hk : ∀ i, 0 < k i) (hsum : HasSum k 1)
    (P : TransitionMatrix) (hP : P.p = mg1Matrix k) (herg : P.PositiveRecurrent) :
    (∀ i : ℕ, i ≠ 0 → meanFirstPassage P i (i - 1) = meanFirstPassage P 1 0) ∧
    (∀ i : ℕ, i ≠ 0 → meanFirstPassage P i 0 = (i : ℝ≥0∞) * meanFirstPassage P 1 0) := by sorry

end FosterQueues.MG1
