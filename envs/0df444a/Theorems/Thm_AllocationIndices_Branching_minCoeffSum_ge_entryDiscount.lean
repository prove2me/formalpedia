-- Prove2me | Theorems.Thm_AllocationIndices_Branching_minCoeffSum_ge_entryDiscount
-- name    : AllocationIndices.Branching.minCoeffSum_ge_entryDiscount
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:39:06.883652+00:00
-- url     : https://prove2.me/theorems/cfd5e2cf-33e7-4fff-801a-9d9410e9e427
-- title:
--   Lemma 5.19(i) — if M − 1 ≥ ψ_i then A(S_i, k) ≥ (M − ψ_i)/(1 − a) · E[a^{T_k^{S_i}/(M−ψ_i)}]
-- statement:
--   Consider the SFABP of §5.7: $n$ arms with disjoint finite state spaces $E_b$ whose union is the set of job types $E = \{1, \dots, N\}$, one transition kernel $P$ under which each $E_b$ is closed and irreducible, discount factor $0 < a < 1$, and $1 \le M \le n$ parallel machines, each processing one arm per period. Let $k$ be an initial state-vector with $k_b \in E_b$. For a job type $i$ let $S_i = \{1, \dots, i\}$, let $B_i$ be the set of arms with no job type in $S_i$ and $\psi_i = |B_i|$, and let
--   $$A(S_i, k) = \min_\pi \sum_{j \in E} A_j^{S_i} x_j^\pi(k)$$
--   be the minimum over all policies of the matrix (5.3) applied to the performance. For an arm $b \notin B_i$ let $T_{k_b}^{S_i}$ be the amount of processing required to move arm $b$ from $k_b$ until it first enters $S_i$ (zero if $k_b \in S_i$), and $T_k^{S_i} = \sum_{b \notin B_i} T_{k_b}^{S_i}$, the arms evolving independently. If $M - 1 \ge \psi_i$ then
--   $$A(S_i, k) \ge \frac{M - \psi_i}{1 - a}\, E\Big[a^{T_k^{S_i}/(M - \psi_i)}\Big].$$
--
--   This lower bound, fed into (5.26), gives the upper bound of Corollary 5.20 on the optimal return.
--
--   **Formalization Note** Job types are `Fin (N + 1)` and $S_i$ is `Iic i`; the hypothesis $M - 1 \ge \psi_i$ is `psi arm i ≤ M - 1` with $M \ge 1$. The minimum is the infimum `minCoeffSum` over all policies on $M$ machines. The expectation is `aggregateEntryDiscount`: an integral against the product of the arms' chain laws, with the real exponent $T/(M - \psi_i)$ and $a^\infty = 0$. The book's standing assumption "$M$ exceeds $n$" is reversed (finding F1); the hypothesis here is $1 \le M \le n$.
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033, §5.7 p. 140, Lemma 5.19(i)

import Definitions.Def_AllocationIndices_Branching_Parallel

open MeasureTheory ProbabilityTheory BanditAlgorithm Finset

namespace AllocationIndices.Branching

/-- Lemma 5.19(i) (p. 140): if `M − 1 ≥ ψ_i` then
`A(S_i, k) ≥ (M − ψ_i)/(1 − a) · E[a^{T_k^{S_i}/(M − ψ_i)}]`. -/
theorem minCoeffSum_ge_entryDiscount {N n M : ℕ} (P : Kernel (Fin (N + 1)) (Fin (N + 1)))
    [IsMarkovKernel P] (arm : Fin (N + 1) → Fin n) (hP : IsArmFamily P arm)
    (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) (hM : 1 ≤ M) (hMn : M ≤ n)
    (k : Fin n → Fin (N + 1)) (hk : ∀ b, arm (k b) = b) (i : Fin (N + 1))
    (hψ : psi arm i ≤ M - 1) :
    ((M : ℝ) - psi arm i) / (1 - a) *
        aggregateEntryDiscount P a arm k i ((M : ℝ) - psi arm i) ≤
      minCoeffSum P M a k (Iic i) := by sorry

end AllocationIndices.Branching
