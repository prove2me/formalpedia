-- Prove2me | Theorems.Thm_AllocationIndices_achievable_region_theorem
-- name    : AllocationIndices.achievable_region_theorem
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T02:58:01.578754+00:00
-- url     : https://prove2.me/theorems/cc500be5-9b19-4d6c-835c-8267496ae4e2
-- title:
--   Theorem 5.5: for a GCL(1) system the achievable region is the polytope P(A, b), its extreme points are permutation performances, and AG(A, r) gives an optimal index policy
-- statement:
--   **Theorem 5.5.** If a system satisfies GCL(1) with performance $x^\pi$, base function $b$ and matrix $A$, then the achievable region $X$ is the convex polytope
--   $$P(A, b) = \Big\{x \in \mathbb{R}_+^N : \sum_{i \in S} A_i^S x_i \ge b(S),\ S \subset E, \text{ and } \sum_{i \in E} A_i^E x_i = b(E)\Big\},$$
--   whose extreme points are the performances of permutation policies. Further, $R^{opt} = \max_\pi \sum_i r_i x_i^\pi$ is achieved by a Gittins index policy $\pi_G$ determined by the indices $(\nu_i, i \in E)$ emerging from adaptive greedy algorithm $AG(A, r)$.
--
--   Formally: for a `GCL1System` whose achievable region is convex (the class of policies is closed under randomization, which the book's argument on convex combinations of extreme points uses and without which $X = P$ fails already for two job types) and any reward vector $r$: $X = P(A, b)$; every extreme point of $P(A, b)$ is $x^\sigma$ for some permutation policy $\sigma$; $AG(A, r)$ has an output; and for every output $(\sigma, y)$ of $AG(A, r)$ and every policy $\pi$, $\sum_i r_i x_i^\pi \le \sum_i r_i x_i^\sigma$. The last clause is the index theorem in this generality: the permutation policy listing the job types in the order found by $AG(A, r)$, the Gittins index policy, is optimal for the linear objective.
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033, §5.4 pp. 127-128, Theorem 5.5 (Bertsimas and Niño-Mora 1996), whose proof is the argument of §5.3 from Lemma 5.1 through complementary slackness (pp. 121-124)

import Definitions.Def_AllocationIndices_Achievable

open MeasureTheory ProbabilityTheory BanditAlgorithm Finset

namespace AllocationIndices

/-- **Theorem 5.5** (p. 127). For a system satisfying GCL(1) with performance `xᵖ`, base function
`b` and matrix `A`, whose class of policies is closed under randomization (the achievable region
is convex, as for past-measurable policies that may randomize; this is what the argument of
§5.2 on convex combinations of extreme points uses), the achievable region is the polytope
`P(A, b)`, its extreme points are performances of permutation policies, and for every reward
vector `r` the optimal return `R^{opt} = max_π ∑ rᵢ xᵢᵖ` is achieved by a Gittins index policy
determined by the adaptive greedy algorithm `AG(A, r)`: an output exists, and every output's
permutation policy attains the maximum. -/
theorem achievable_region_theorem {N : ℕ} {Pol : Type*} (D : GCL1System N Pol)
    (hconv : Convex ℝ (Set.range D.perf)) (r : Fin N → ℝ) :
    Set.range D.perf = achievablePolytope D.A D.b ∧
    (∀ x ∈ Set.extremePoints ℝ (achievablePolytope D.A D.b),
      ∃ σ : Equiv.Perm (Fin N), x = D.perf (D.permPolicy σ)) ∧
    (∃ (σ : Equiv.Perm (Fin N)) (y : Fin N → ℝ), IsAdaptiveGreedy D.A r σ y) ∧
    (∀ (σ : Equiv.Perm (Fin N)) (y : Fin N → ℝ), IsAdaptiveGreedy D.A r σ y →
      ∀ π, linearObjective r (D.perf π) ≤ linearObjective r (D.perf (D.permPolicy σ))) := by sorry

end AllocationIndices
