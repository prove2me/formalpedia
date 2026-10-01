-- Prove2me | Theorems.Thm_AllocationIndices_sfabp_conservation_laws
-- name    : AllocationIndices.sfabp_conservation_laws
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T02:53:28.513661+00:00
-- url     : https://prove2.me/theorems/fc310f44-720a-4664-994c-9a5f792fd998
-- title:
--   Lemma 5.1: a SFABP satisfies the conservation laws (5.5)-(5.6), with equality for policies giving priority to states outside S
-- statement:
--   **Lemma 5.1.** There exist positive $A_i^S$ ($i \in S \subseteq E$), having the interpretation (5.3), such that for any scheduling policy $\pi$, $\sum_{i \in S} A_i^S x_i^\pi \ge b(S)$ for all $S \subset E$ (5.5), $\sum_{i \in E} A_i^E x_i^\pi = b(E)$ (5.6), and such that equality holds in (5.5) if $\pi$ is a policy that gives priority to bandits whose states are not in $S$ over any bandits whose states are in $S$.
--
--   Formally: for $n$ identical bandit processes on $E = \{1, \dots, N\}$ with kernel $P$, discount factor $a \in (0, 1)$, initial state-vector $k$, every policy $\pi$ of the Bandit Algorithms model and every $S \subseteq E$: $A_i^S > 0$ for $i \in S$; $\sum_{i \in S} A_i^S x_i^\pi \ge b(S)$; $\sum_{i \in E} x_i^\pi = 1/(1-a)$ (which is (5.6), as $A_i^E = 1$ and $b(E) = 1/(1-a)$); and if $\pi$ gives priority to bandits whose states are not in $S$, then $\sum_{i \in S} A_i^S x_i^\pi = b(S)$. Here $b(S) = (1-a)^{-1} \prod_{j : k_j \notin S} \mathbb{E}[a^{T^S_{k_j}}]$, the minimal cost identified on p. 120 (the printed formula has a sum in place of the product).
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033, §5.3 pp. 120-121, Lemma 5.1 with the argument preceding it ((5.3), the cost problem and its value)

import Definitions.Def_AllocationIndices_Achievable

open MeasureTheory ProbabilityTheory BanditAlgorithm Finset

namespace AllocationIndices

/-- **Lemma 5.1** (p. 120). For a SFABP of `n` identical bandits on the finite state space
`E = Fin N` with discount factor `a ∈ (0, 1)`, started from the state-vector `k`, the
coefficients `Aᵢ^S` of (5.3) are positive for `i ∈ S`, and for every scheduling policy `π`,
`∑_{i∈S} Aᵢ^S xᵢᵖ ≥ b(S)` for every `S ⊆ E` (5.5), `∑_{i∈E} Aᵢ^E xᵢᵖ = b(E) = 1/(1−a)` (5.6),
and equality holds in (5.5) whenever `π` gives priority to bandits whose states are not in `S`
over any bandits whose states are in `S`. -/
theorem sfabp_conservation_laws {N n : ℕ} (P : Kernel (Fin N) (Fin N)) [IsMarkovKernel P]
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (k : Fin n → Fin N) (π : MarkovBanditPolicy n (Fin N))
    (S : Finset (Fin N)) :
    (∀ i ∈ S, 0 < conservationCoeff P a S i) ∧
    conservationBase P a k S ≤ ∑ i ∈ S, conservationCoeff P a S i * performance P π a k i ∧
    ∑ i, performance P π a k i = (1 - a)⁻¹ ∧
    (GivesPriority S π →
      ∑ i ∈ S, conservationCoeff P a S i * performance P π a k i = conservationBase P a k S) := by sorry

end AllocationIndices
