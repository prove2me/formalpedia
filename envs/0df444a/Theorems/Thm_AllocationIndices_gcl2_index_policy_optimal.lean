-- Prove2me | Theorems.Thm_AllocationIndices_gcl2_index_policy_optimal
-- name    : AllocationIndices.gcl2_index_policy_optimal
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T02:55:55.011986+00:00
-- url     : https://prove2.me/theorems/a481cd67-e41f-4d8a-aab1-9c56a0b6cc3c
-- title:
--   Theorem 5.10: for a GCL(2) system the achievable region is P'(F, f), its extreme points are permutation performances, and AG(F, c) gives a cost-minimizing index policy
-- statement:
--   **Theorem 5.10.** If a system satisfies GCL(2) with performance $x^\pi$, base function $f$ and matrix $F$, then the achievable region is the convex polytope $P'(F, f)$, whose extreme points are the performances of permutation policies. Further, $C^{opt} = \min_\pi \sum_i c_i x_i^\pi$ is achieved by a Gittins index policy $\pi_G$ determined by the indices emerging from the adaptive greedy algorithm $AG(F, c)$.
--
--   Formally: for a `GCL2System` whose achievable region is convex (the class of policies is closed under randomization, as the book's argument on convex combinations of extreme points requires) and any cost vector $c$: $X = P'(F, f)$; every extreme point of $P'(F, f)$ is $x^\sigma$ for some permutation policy $\sigma$; $AG(F, c)$ has an output; and for every output $(\sigma, y)$ and every policy $\pi$, $\sum_i c_i x_i^\sigma \le \sum_i c_i x_i^\pi$.
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033, §5.4 p. 130, Theorem 5.10 (Bertsimas and Niño-Mora 1996)

import Definitions.Def_AllocationIndices_Achievable

open MeasureTheory ProbabilityTheory BanditAlgorithm Finset

namespace AllocationIndices

/-- **Theorem 5.10** (p. 130). For a system satisfying GCL(2) with performance `xᵖ`, base
function `f` and matrix `F`, whose class of policies is closed under randomization, the
achievable region is the polytope `P'(F, f)`, its extreme points are performances of permutation
policies, and for every cost vector `c` the optimal cost `C^{opt} = min_π ∑ cᵢ xᵢᵖ` is achieved
by a Gittins index policy determined by the adaptive greedy algorithm `AG(F, c)`. -/
theorem gcl2_index_policy_optimal {N : ℕ} {Pol : Type*} (D : GCL2System N Pol)
    (hconv : Convex ℝ (Set.range D.perf)) (c : Fin N → ℝ) :
    Set.range D.perf = achievablePolytope' D.F D.f ∧
    (∀ x ∈ Set.extremePoints ℝ (achievablePolytope' D.F D.f),
      ∃ σ : Equiv.Perm (Fin N), x = D.perf (D.permPolicy σ)) ∧
    (∃ (σ : Equiv.Perm (Fin N)) (y : Fin N → ℝ), IsAdaptiveGreedy D.F c σ y) ∧
    (∀ (σ : Equiv.Perm (Fin N)) (y : Fin N → ℝ), IsAdaptiveGreedy D.F c σ y →
      ∀ π, linearObjective c (D.perf (D.permPolicy σ)) ≤ linearObjective c (D.perf π)) := by sorry

end AllocationIndices
