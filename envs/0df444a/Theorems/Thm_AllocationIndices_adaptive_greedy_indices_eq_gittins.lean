-- Prove2me | Theorems.Thm_AllocationIndices_adaptive_greedy_indices_eq_gittins
-- name    : AllocationIndices.adaptive_greedy_indices_eq_gittins
-- status  : Open
-- author  : @naimengye
-- created : 2026-09-24T02:54:00.257637+00:00
-- url     : https://prove2.me/theorems/965ab2d9-398d-4dca-9a6c-d737d8ee9fa7
-- title:
--   p. 123: the indices computed by the adaptive greedy algorithm AG(A, r) for a SFABP are nondecreasing along its order and equal the Gittins indices
-- statement:
--   **p. 123.** The algorithm calculates $\nu_{i_j}$s, with $r_{i_N} = \nu_{i_N} \ge \nu_{i_{N-1}} \ge \cdots \ge \nu_{i_1}$. These are in fact the Gittins indices.
--
--   Formally: for a bandit process on $E = \{1, \dots, N\}$ with kernel $P$, rewards $r$ and discount factor $a \in (0, 1)$, let $A_i^S = \mathbb{E}[1 + a + \cdots + a^{T_i^S - 1}]$ be the coefficients (5.3). For every output $(\sigma, y)$ of the adaptive greedy algorithm $AG(A, r)$ (any tie-breaking), the indices $\nu_{i_k} = \sum_{j \ge k} \bar y_{S_j}$ satisfy $\nu_{i_1} \le \nu_{i_2} \le \cdots \le \nu_{i_N}$, and $\nu_i = \nu(B, i)$, the Gittins index of state $i$, for every state $i$. (That $\nu_{i_N} = r_{i_N}$ is immediate from $A_i^E = 1$ and is not restated.)
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033, §5.3 pp. 122-123, the adaptive greedy algorithm AG(A, r) and the identification (5.13)-(5.14) of its output with the Gittins indices

import Definitions.Def_AllocationIndices_Achievable

open MeasureTheory ProbabilityTheory BanditAlgorithm Finset

namespace AllocationIndices

/-- **The adaptive greedy indices are the Gittins indices** (p. 123, Eqs. (5.13)–(5.14)). For a
bandit process on the finite state space `E = Fin N` with transition kernel `P`, rewards `r` and
discount factor `a ∈ (0, 1)`, let `A` be the matrix (5.3) of expected discounted return times.
Every output `(σ, y)` of the adaptive greedy algorithm `AG(A, r)` lists the states in
nondecreasing order of its indices, `ν_{i_1} ≤ ν_{i_2} ≤ ⋯ ≤ ν_{i_N}`, and these indices are
the Gittins indices: `ν_i = ν(B, i)` for every state `i`. -/
theorem adaptive_greedy_indices_eq_gittins {N : ℕ} (P : Kernel (Fin N) (Fin N))
    [IsMarkovKernel P] (r : Fin N → ℝ) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (σ : Equiv.Perm (Fin N)) (y : Fin N → ℝ) (h : IsAdaptiveGreedy (conservationCoeff P a) r σ y) :
    (∀ j k : Fin N, j ≤ k → greedyIndex σ y (σ j) ≤ greedyIndex σ y (σ k)) ∧
    ∀ i, greedyIndex σ y i = gittinsIndex P r a i := by sorry

end AllocationIndices
