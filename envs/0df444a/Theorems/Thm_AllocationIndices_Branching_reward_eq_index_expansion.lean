-- Prove2me | Theorems.Thm_AllocationIndices_Branching_reward_eq_index_expansion
-- name    : AllocationIndices.Branching.reward_eq_index_expansion
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:39:06.983598+00:00
-- url     : https://prove2.me/theorems/d8060d43-5169-4373-be5c-2cd71002d35f
-- title:
--   Eq. (5.21), as recalled on p. 139 — r_j = ν_N − Σ_{i=j}^{N−1} (ν_{i+1} − ν_i) A_j^{S_i}
-- statement:
--   Let $P$ be a Markov kernel on the finite set of job types $E = \{1, \dots, N\}$, let $0 < a < 1$, and let $A = (A_i^S)$ be the SFABP matrix (5.3) of §5.3: $A_i^S = E[1 + a + \cdots + a^{T_i^S - 1}]$ for $i \in S$, with $T_i^S \ge 1$ the return time of the chain from $i$ to $S$, and $A_i^S = 0$ for $i \notin S$. Let $r \in \mathbb{R}^E$ be a reward vector, and suppose the job types are numbered in the order produced by the adaptive greedy algorithm $\mathrm{AG}(A, r)$ of p. 122, i.e. the algorithm, run with dual variables $\bar y_{S_N}, \dots, \bar y_{S_1}$, picks job type $N$ first, then $N - 1$, and so on, where $S_i = \{1, \dots, i\}$. Its indices are $\nu_i = \bar y_{S_N} + \cdots + \bar y_{S_i}$. Then for every job type $j$,
--   $$r_j = \nu_N - \sum_{i=j}^{N-1} (\nu_{i+1} - \nu_i)\, A_j^{S_i}.$$
--
--   This is (5.21), $r_j = \sum_{i=j}^N \xi_i A_j^{S_i}$ with $\xi_N = \nu_N$ and $\xi_i = \nu_i - \nu_{i+1}$, rewritten with $A_j^E = 1$; it expresses each reward through the indices and is the identity from which the return of any policy is computed in (5.25).
--
--   **Formalization Note** Job types are `Fin (N + 1)` (the book's $N$ is Lean's `N + 1`, job type $i$ is the index `i - 1`). The numbering hypothesis is `IsAdaptiveGreedy (conservationCoeff P a) r (Equiv.refl _) y`: the identity permutation is an output of $\mathrm{AG}(A, r)$ with dual variables `y` (`y i` $= \bar y_{S_{i+1}}$), and $\nu_i$ is `greedyIndex (Equiv.refl _) y i`. The sum over $i = j, \dots, N - 1$ is the sum over `i : Fin N` with `j ≤ i.castSucc`, with $\nu_{i+1}$ = `ν i.succ` and $S_i$ = `Iic i.castSucc`.
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033, §5.7 p. 139, display recalling Eq. (5.21) (p. 133) with A_i^E = 1

import Definitions.Def_AllocationIndices_Branching_Parallel

open MeasureTheory ProbabilityTheory BanditAlgorithm Finset

namespace AllocationIndices.Branching

/-- Eq. (5.21) in the form recalled on p. 139: when the job types are numbered in the order produced
by the adaptive greedy algorithm `AG(A, r)` for the SFABP matrix `A` of (5.3) (here `Aᵢ^E = 1`),
`r_j = ν_N − ∑_{i=j}^{N−1} (ν_{i+1} − ν_i) A_j^{S_i}` for every job type `j`. -/
theorem reward_eq_index_expansion {N : ℕ} (P : Kernel (Fin (N + 1)) (Fin (N + 1)))
    [IsMarkovKernel P] (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) (r : Fin (N + 1) → ℝ)
    (y : Fin (N + 1) → ℝ)
    (hAG : IsAdaptiveGreedy (conservationCoeff P a) r (Equiv.refl (Fin (N + 1))) y)
    (j : Fin (N + 1)) :
    r j = greedyIndex (Equiv.refl (Fin (N + 1))) y (Fin.last N) -
      ∑ i ∈ univ.filter (fun i : Fin N ↦ j ≤ i.castSucc),
        (greedyIndex (Equiv.refl (Fin (N + 1))) y i.succ -
          greedyIndex (Equiv.refl (Fin (N + 1))) y i.castSucc) *
          conservationCoeff P a (Iic i.castSucc) j := by sorry

end AllocationIndices.Branching
