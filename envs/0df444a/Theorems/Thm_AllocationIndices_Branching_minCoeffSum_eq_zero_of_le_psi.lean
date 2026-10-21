-- Prove2me | Theorems.Thm_AllocationIndices_Branching_minCoeffSum_eq_zero_of_le_psi
-- name    : AllocationIndices.Branching.minCoeffSum_eq_zero_of_le_psi
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:39:09.015586+00:00
-- url     : https://prove2.me/theorems/60bbcd9f-a569-4be1-99f9-2d5e5a6ef4dd
-- title:
--   Lemma 5.19(ii) — if ψ_i ≥ M then A(S_i, k) = 0
-- statement:
--   Consider the SFABP of §5.7: $n$ arms with disjoint finite state spaces $E_b$ whose union is the set of job types $E = \{1, \dots, N\}$, one transition kernel $P$ under which each $E_b$ is closed and irreducible, discount factor $0 < a < 1$, and $1 \le M \le n$ parallel machines, each processing one arm per period. Let $k$ be an initial state-vector with $k_b \in E_b$. For a job type $i$ let $S_i = \{1, \dots, i\}$, let $\psi_i$ be the number of arms with no job type in $S_i$, and let
--   $$A(S_i, k) = \min_\pi \sum_{j \in E} A_j^{S_i} x_j^\pi(k),$$
--   the minimum over all policies of the matrix (5.3) applied to the performance. If $\psi_i \ge M$ then
--   $$A(S_i, k) = 0.$$
--
--   When $\psi_i \ge M$ there are enough arms that never visit $S_i$ to keep every machine busy, so a policy can avoid $S_i$ altogether.
--
--   **Formalization Note** Job types are `Fin (N + 1)` and $S_i$ is `Iic i`; `psi arm i` counts the arms all of whose job types exceed `i`. The minimum is the infimum `minCoeffSum` over all policies on $M$ machines. The book assumes "the number of parallel servers $M$ exceeds the number of arms $n$" (p. 139), which is reversed (finding F1): with $M > n$ no arm set of size $M$ exists, $\psi_i \le n < M$, and the lemma is empty; the hypothesis here is $1 \le M \le n$.
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033, §5.7 p. 140, Lemma 5.19(ii)

import Definitions.Def_AllocationIndices_Branching_Parallel

open MeasureTheory ProbabilityTheory BanditAlgorithm Finset

namespace AllocationIndices.Branching

/-- Lemma 5.19(ii) (p. 140): if `ψ_i ≥ M` then `A(S_i, k) = 0`. -/
theorem minCoeffSum_eq_zero_of_le_psi {N n M : ℕ} (P : Kernel (Fin (N + 1)) (Fin (N + 1)))
    [IsMarkovKernel P] (arm : Fin (N + 1) → Fin n) (hP : IsArmFamily P arm)
    (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) (hM : 1 ≤ M) (hMn : M ≤ n)
    (k : Fin n → Fin (N + 1)) (hk : ∀ b, arm (k b) = b) (i : Fin (N + 1))
    (hψ : M ≤ psi arm i) :
    minCoeffSum P M a k (Iic i) = 0 := by sorry

end AllocationIndices.Branching
