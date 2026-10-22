-- Prove2me | Theorems.Thm_AllocationIndices_Branching_suboptimality_le_coeffSum_gap
-- name    : AllocationIndices.Branching.suboptimality_le_coeffSum_gap
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:39:08.326683+00:00
-- url     : https://prove2.me/theorems/9620c0c1-99be-4759-9ade-63fe402ad28d
-- title:
--   Eq. (5.27) — R^opt(k) − Rᵖ(k) ≤ Σ_{i=1}^{N−1} (ν_{i+1} − ν_i)[Aᵖ(S_i, k) − A(S_i, k)]
-- statement:
--   Consider the SFABP of §5.7: $n$ arms with disjoint finite state spaces $E_b$ whose union is the set of job types $E = \{1, \dots, N\}$, one transition kernel $P$ under which each $E_b$ is closed and irreducible, discount factor $0 < a < 1$, reward vector $r$, and $1 \le M \le n$ parallel machines, each processing one arm per period. Suppose the job types are numbered in ascending order of the indices $\nu_1 \le \nu_2 \le \cdots \le \nu_N$ produced by the adaptive greedy algorithm $\mathrm{AG}(A, r)$ for the SFABP matrix (5.3), and write $S_i = \{1, \dots, i\}$. Let $k$ be an initial state-vector with $k_b \in E_b$. Then every policy $\pi$ satisfies
--   $$R^{\mathrm{opt}}(k) - R^\pi(k) \le \sum_{i=1}^{N-1} (\nu_{i+1} - \nu_i)\big[A^\pi(S_i, k) - A(S_i, k)\big],$$
--   where $R^{\mathrm{opt}}(k) = \sup_\pi R^\pi(k)$, $A^\pi(S, k) = \sum_{j \in E} A_j^S x_j^\pi(k)$ and $A(S, k) = \min_\pi A^\pi(S, k)$.
--
--   The bound measures the suboptimality of a policy by how far it is from minimizing each $A^\pi(S_i, k)$; for $M = 1$ the Gittins index policy attains every minimum.
--
--   **Formalization Note** Job types are `Fin (N + 1)` (the book's $N$ is Lean's `N + 1`); the sum over $i = 1, \dots, N - 1$ is over `i : Fin N`, with $\nu_{i+1}$ = `ν i.succ`, $\nu_i$ = `ν i.castSucc` and $S_i$ = `Iic i.castSucc`. The numbering is the hypothesis that the identity permutation is an output of $\mathrm{AG}(A, r)$ together with `Monotone ν`. $R^{\mathrm{opt}}$ and $A(S, k)$ are the supremum and infimum over all policies on $M$ machines (`optimalReturn`, `minCoeffSum`). The book's standing assumption "$M$ exceeds $n$" is reversed (finding F1); the hypothesis here is $1 \le M \le n$.
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033, §5.7 p. 140, Eq. (5.27)

import Definitions.Def_AllocationIndices_Branching_Parallel

open MeasureTheory ProbabilityTheory BanditAlgorithm Finset

namespace AllocationIndices.Branching

/-- Eq. (5.27) (p. 140): the reward suboptimality of any policy `π` on `M` parallel machines is at
most `∑_{i=1}^{N−1} (ν_{i+1} − ν_i) [Aᵖ(S_i, k) − A(S_i, k)]`. -/
theorem suboptimality_le_coeffSum_gap {N n M : ℕ} (P : Kernel (Fin (N + 1)) (Fin (N + 1)))
    [IsMarkovKernel P] (arm : Fin (N + 1) → Fin n) (hP : IsArmFamily P arm)
    (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) (hM : 1 ≤ M) (hMn : M ≤ n)
    (r : Fin (N + 1) → ℝ) (y : Fin (N + 1) → ℝ)
    (hAG : IsAdaptiveGreedy (conservationCoeff P a) r (Equiv.refl (Fin (N + 1))) y)
    (hmono : Monotone (greedyIndex (Equiv.refl (Fin (N + 1))) y))
    (k : Fin n → Fin (N + 1)) (hk : ∀ b, arm (k b) = b) (π : ParallelPolicy n N M) :
    optimalReturn P M a r k - parallelReturn P π a r k ≤
      ∑ i : Fin N,
        (greedyIndex (Equiv.refl (Fin (N + 1))) y i.succ -
          greedyIndex (Equiv.refl (Fin (N + 1))) y i.castSucc) *
          (coeffSum P π a k (Iic i.castSucc) - minCoeffSum P M a k (Iic i.castSucc)) := by sorry

end AllocationIndices.Branching
