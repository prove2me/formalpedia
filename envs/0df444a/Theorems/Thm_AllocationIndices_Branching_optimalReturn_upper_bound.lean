-- Prove2me | Theorems.Thm_AllocationIndices_Branching_optimalReturn_upper_bound
-- name    : AllocationIndices.Branching.optimalReturn_upper_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:39:09.863523+00:00
-- url     : https://prove2.me/theorems/a351786c-b3f0-4166-95df-c52294374541
-- title:
--   Corollary 5.20 — upper bound on the optimal return of a SFABP on M parallel machines
-- statement:
--   Consider the simple family of alternative bandit processes of §5.7 on $M$ parallel machines. There are $n$ arms; arm $b$ has a finite state space $E_b$, the $E_b$ are disjoint and their union is the set of job types $E = \{1, \dots, N\}$; one transition kernel $P$ moves a processed arm, every $E_b$ is closed under $P$ and $P$ is irreducible on it. Time is discrete with discount factor $0 < a < 1$, $r$ is a reward vector, and $1 \le M \le n$ machines each process one arm per period, the unprocessed arms being frozen. Let $k$ be the initial state-vector, $k_b \in E_b$.
--
--   Suppose the job types are numbered in ascending order $\nu_1 \le \cdots \le \nu_N$ of the indices produced by the adaptive greedy algorithm $\mathrm{AG}(A, r)$ for the SFABP matrix $A$ of (5.3), and write $S_i = \{1, \dots, i\}$. Let $i_b = \min E_b$ be the job type of lowest index of arm $b$, and suppose the arms are numbered so that $i_1 \le i_2 \le \cdots \le i_n$. Let $\psi_i$ be the number of arms with no job type in $S_i$, and for the other arms let $T_k^{S_i} = \sum_{b} T_{k_b}^{S_i}$ be the total amount of processing needed to bring each of them from its initial state into $S_i$ for the first time, the arms evolving independently. Then the optimal return $R^{\mathrm{opt}}(k) = \sup_\pi \sum_{i \in E} r_i x_i^\pi(k)$ over all policies satisfies
--   $$R^{\mathrm{opt}}(k) \le \nu_N \Big(\frac{M}{1-a}\Big) - \Big(\frac{1}{1-a}\Big) \sum_{i = i_{n-M+1}}^{N-1} (\nu_{i+1} - \nu_i)(M - \psi_i)\, E\Big[a^{T_k^{S_i}/(M - \psi_i)}\Big].$$
--
--   Combined with an exact or lower-bound expression for the return of a given policy, such as the index heuristic $\pi_G^*$ of p. 143, the bound gives explicit suboptimality bounds for index policies on parallel machines.
--
--   **Formalization Note** Job types are `Fin (N + 1)`, so the book's $N$ is Lean's `N + 1` and the book's job type $i$ is the index `i - 1`; the sum over $i = i_{n-M+1}, \dots, N - 1$ is over `i : Fin N` with `lowest ⟨n - M, _⟩ ≤ i.castSucc`, with $\nu_{i+1}$ = `ν i.succ`, $\nu_i$ = `ν i.castSucc`, $S_i$ = `Iic i.castSucc`. The numbering of job types is the hypothesis that the identity permutation is an output of $\mathrm{AG}(A, r)$ (`IsAdaptiveGreedy`, dual variables `y`) together with `Monotone ν`, $\nu$ = `greedyIndex (Equiv.refl _) y`; the numbering of arms is `lowest b` $= i_b$ with `Monotone lowest`. $R^{\mathrm{opt}}$ is the supremum `optimalReturn` over all policies on $M$ machines, and the expectation is `aggregateEntryDiscount`, an integral against the product of the arms' chain laws with a real exponent and $a^\infty = 0$. The model is the book's discrete-time one (discount factor $a$), so no unit conversion is made. The book's standing assumption that "the number of parallel servers $M$ exceeds the number of arms $n$" (p. 139) is reversed (finding F1: with $M > n$ the arm index $n - M + 1$ is not positive); the hypothesis here is $1 \le M \le n$.
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033, §5.7 p. 142, Corollary 5.20

import Definitions.Def_AllocationIndices_Branching_Parallel

open MeasureTheory ProbabilityTheory BanditAlgorithm Finset

namespace AllocationIndices.Branching

/-- Corollary 5.20 (p. 142): for the SFABP on `M` parallel machines, with job types numbered in
ascending order of their `AG(A, r)` indices and arms numbered so that `i_1 ≤ ⋯ ≤ i_n`
(`i_b` the job type of lowest index of arm `b`),
`R^opt(k) ≤ ν_N M/(1 − a) − (1/(1 − a)) ∑_{i=i_{n−M+1}}^{N−1} (ν_{i+1} − ν_i)(M − ψ_i) E[a^{T_k^{S_i}/(M−ψ_i)}]`. -/
theorem optimalReturn_upper_bound {N n M : ℕ} (P : Kernel (Fin (N + 1)) (Fin (N + 1)))
    [IsMarkovKernel P] (arm : Fin (N + 1) → Fin n) (hP : IsArmFamily P arm)
    (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) (hM : 1 ≤ M) (hMn : M ≤ n)
    (r : Fin (N + 1) → ℝ) (y : Fin (N + 1) → ℝ)
    (hAG : IsAdaptiveGreedy (conservationCoeff P a) r (Equiv.refl (Fin (N + 1))) y)
    (hmono : Monotone (greedyIndex (Equiv.refl (Fin (N + 1))) y))
    (lowest : Fin n → Fin (N + 1))
    (hlowest : ∀ b, arm (lowest b) = b ∧ ∀ j, arm j = b → lowest b ≤ j)
    (hnum : Monotone lowest)
    (k : Fin n → Fin (N + 1)) (hk : ∀ b, arm (k b) = b) :
    optimalReturn P M a r k ≤
      greedyIndex (Equiv.refl (Fin (N + 1))) y (Fin.last N) * ((M : ℝ) / (1 - a)) -
      1 / (1 - a) *
        ∑ i ∈ univ.filter (fun i : Fin N ↦
            lowest ⟨n - M, Nat.sub_lt (lt_of_lt_of_le hM hMn) hM⟩ ≤ i.castSucc),
          (greedyIndex (Equiv.refl (Fin (N + 1))) y i.succ -
            greedyIndex (Equiv.refl (Fin (N + 1))) y i.castSucc) *
            ((M : ℝ) - psi arm i.castSucc) *
            aggregateEntryDiscount P a arm k i.castSucc ((M : ℝ) - psi arm i.castSucc) := by sorry

end AllocationIndices.Branching
