-- Prove2me | Theorems.Thm_AllocationIndices_Branching_return_eq_coeffSum_expansion
-- name    : AllocationIndices.Branching.return_eq_coeffSum_expansion
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:39:06.113303+00:00
-- url     : https://prove2.me/theorems/76ce0c51-6cc0-4cd1-b9c1-7e9f926a8325
-- title:
--   Eq. (5.25) — Rᵖ(k) = ν_N M/(1 − a) − Σ_{i=1}^{N−1} (ν_{i+1} − ν_i) Aᵖ(S_i, k) on M parallel machines
-- statement:
--   Consider $n$ arms on the job types $E = \{1, \dots, N\}$ with transition kernel $P$, discount factor $0 < a < 1$, reward vector $r$, and $M$ parallel machines, each processing one arm per period, as in the model of §5.7. Let $A$ be the SFABP matrix (5.3), and suppose the job types are numbered in the order produced by the adaptive greedy algorithm $\mathrm{AG}(A, r)$, with indices $\nu_1, \dots, \nu_N$, so that $S_i = \{1, \dots, i\}$. Then for every policy $\pi$ and every initial state-vector $k$,
--   $$R^\pi(k) = \sum_{i \in E} r_i x_i^\pi(k) = \nu_N \Big(\frac{M}{1 - a}\Big) - \sum_{i=1}^{N-1} (\nu_{i+1} - \nu_i)\, A^\pi(S_i, k),$$
--   where $x_i^\pi(k)$ is the expected total discounted number of times a job of type $i$ is processed and $A^\pi(S, k) = \sum_{i \in E} A_i^S x_i^\pi(k)$.
--
--   The identity reduces the return of any parallel-machine policy to the $N - 1$ quantities $A^\pi(S_i, k)$; minimizing each of them separately gives the bound (5.26) on the optimal return.
--
--   **Formalization Note** Job types are `Fin (N + 1)` (the book's $N$ is Lean's `N + 1`); the sum over $i = 1, \dots, N - 1$ is over `i : Fin N`, with $\nu_{i+1}$ = `ν i.succ`, $\nu_i$ = `ν i.castSucc`, $S_i$ = `Iic i.castSucc`, and $\nu_N$ = `ν (Fin.last N)`. The numbering hypothesis is that the identity permutation is an output of $\mathrm{AG}(A, r)$ (`IsAdaptiveGreedy … (Equiv.refl _) y`), and $\nu$ is `greedyIndex (Equiv.refl _) y`. The statement is made for all policies of the model (`ParallelPolicy n N M`); none exists when $M > n$. The book's standing assumptions on the arms (closed, irreducible state spaces, $n$ versus $M$) are not needed for this identity and are not assumed.
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033, §5.7 p. 139, Eq. (5.25)

import Definitions.Def_AllocationIndices_Branching_Parallel

open MeasureTheory ProbabilityTheory BanditAlgorithm Finset

namespace AllocationIndices.Branching

/-- Eq. (5.25) (p. 139): for every policy `π` on `M` parallel machines,
`Rᵖ(k) = ν_N M/(1 − a) − ∑_{i=1}^{N−1} (ν_{i+1} − ν_i) Aᵖ(S_i, k)`. -/
theorem return_eq_coeffSum_expansion {N n M : ℕ} (P : Kernel (Fin (N + 1)) (Fin (N + 1)))
    [IsMarkovKernel P] (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) (r : Fin (N + 1) → ℝ)
    (y : Fin (N + 1) → ℝ)
    (hAG : IsAdaptiveGreedy (conservationCoeff P a) r (Equiv.refl (Fin (N + 1))) y)
    (k : Fin n → Fin (N + 1)) (π : ParallelPolicy n N M) :
    parallelReturn P π a r k =
      greedyIndex (Equiv.refl (Fin (N + 1))) y (Fin.last N) * ((M : ℝ) / (1 - a)) -
      ∑ i : Fin N,
        (greedyIndex (Equiv.refl (Fin (N + 1))) y i.succ -
          greedyIndex (Equiv.refl (Fin (N + 1))) y i.castSucc) *
          coeffSum P π a k (Iic i.castSucc) := by sorry

end AllocationIndices.Branching
